// Entry point: boot the forge, register it with the trial env, and wait until
// the env says the trial is over. The env drives the whole lifecycle; this
// file only speaks its small protocol (register, then poll /done) and never
// decides anything about the forge itself, which lives in app.ts.

import { createApp } from "./app.ts";

// The env's origin, without a trailing slash. Empty means there is no env to
// talk to, and the process cannot do anything useful.
const envOrigin = (process.env.MAKEFUN_ENV_URL ?? "").replace(/\/+$/, "");
if (envOrigin === "") {
  process.stderr.write("[entry] MAKEFUN_ENV_URL is empty: no env to register with\n");
  process.exit(1);
}

const REQUEST_BUDGET_MS = 30_000;
const FIRST_PAUSE_MS = 250;
const LONGEST_PAUSE_MS = 2_000;

const pause = (ms: number): Promise<void> =>
  new Promise((resolve) => setTimeout(resolve, ms));

// Pause after the nth failed attempt: doubles from FIRST_PAUSE_MS, never
// longer than LONGEST_PAUSE_MS.
function backoffFor(attempt: number): number {
  return Math.min(LONGEST_PAUSE_MS, FIRST_PAUSE_MS * 2 ** Math.min(attempt, 8));
}

// One register attempt: true when the env answers 200, or 409 (a first
// register already won). 400/405 are contract errors and throw; anything
// else, including a network error, means "try again".
async function tryRegister(port: number): Promise<boolean> {
  try {
    const res = await fetch(`${envOrigin}/register`, {
      method: "POST",
      headers: { "content-type": "application/json" },
      body: JSON.stringify({ port }),
      signal: AbortSignal.timeout(REQUEST_BUDGET_MS),
    });
    if (res.status === 200 || res.status === 409) return true;
    if (res.status === 400 || res.status === 405) {
      throw new Error(`register refused: HTTP ${res.status} ${await res.text()}`);
    }
    return false;
  } catch (err) {
    if (err instanceof Error && err.message.startsWith("register refused: ")) throw err;
    return false;
  }
}

async function register(port: number): Promise<void> {
  for (let attempt = 0; ; attempt += 1) {
    if (await tryRegister(port)) return;
    await pause(backoffFor(attempt));
  }
}

// One /done poll: true only when the env answers {"done": true}.
async function tryDone(): Promise<boolean> {
  try {
    const res = await fetch(`${envOrigin}/done`, {
      signal: AbortSignal.timeout(REQUEST_BUDGET_MS),
    });
    if (!res.ok) return false;
    const body = (await res.json()) as { done?: unknown };
    return body.done === true;
  } catch {
    return false;
  }
}

async function waitUntilDone(): Promise<void> {
  for (let attempt = 0; ; attempt += 1) {
    if (await tryDone()) return;
    await pause(backoffFor(attempt));
  }
}

// Bind an ephemeral port and report it back. Never bind 8080: the env owns it.
function listenEphemeral(server: ReturnType<typeof createApp>): Promise<number> {
  return new Promise<number>((resolve, reject) => {
    server.once("error", reject);
    server.listen(0, () => {
      const address = server.address();
      if (address === null || typeof address === "string") {
        reject(new Error("the server did not bind an ephemeral TCP port"));
        return;
      }
      resolve(address.port);
    });
  });
}

async function boot(): Promise<void> {
  const server = createApp();
  const port = await listenEphemeral(server);
  process.stdout.write(`[entry] bound port ${port}\n`);
  await register(port);
  process.stdout.write("[entry] registered; waiting for the env to finish\n");
  await waitUntilDone();
  server.close();
  process.stdout.write("[entry] env is done\n");
}

try {
  await boot();
  process.exit(0);
} catch (err) {
  process.stderr.write(`[entry] ${err instanceof Error ? err.message : String(err)}\n`);
  process.exit(1);
}
