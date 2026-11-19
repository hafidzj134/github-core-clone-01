// github-core-clone-01: a standalone GitHub-compatible git forge in one process.
// Node 22 standard library only. Serves git smart HTTP (v2 upload-pack, v0
// receive-pack), REST v3, GraphQL v4 and MCP from one in-memory store.
import { createServer, type IncomingMessage, type Server, type ServerResponse } from 'node:http';
import { createHash } from 'node:crypto';
import { deflateSync, inflateSync } from 'node:zlib';

export const VIEWER_LOGIN = 'adaiversen';
export const VIEWER_ID = 1000;
const VIEWER_EMAIL = 'adaiversen@example.invalid';
const ZERO_OID = '0'.repeat(40);
const JSON_TYPE = 'application/json; charset=utf-8';
let reqCounter = 0;

function sha1hex(data: Buffer | string): string {
  return createHash('sha1').update(data).digest('hex');
}
function sha1buf(data: Buffer | string): Buffer {
  return createHash('sha1').update(data).digest();
}
function b64url(s: string): string {
  return Buffer.from(s, 'utf8').toString('base64url');
}
function gid(kind: string, key: string): string {
  return `${kind}_${b64url(sha1hex(`${kind}:${key}`).slice(0, 24))}`;
}
function nowIso(): string {
  return new Date().toISOString();
}

// ---------------------------------------------------------------- pkt-lines
function pkt(payload: string | Buffer): Buffer {
  const b = typeof payload === 'string' ? Buffer.from(payload, 'utf8') : payload;
  const len = b.length + 4;
  return Buffer.concat([Buffer.from(len.toString(16).padStart(4, '0'), 'ascii'), b]);
}
function pktFlush(): Buffer {
  return Buffer.from('0000', 'ascii');
}
function pktDelim(): Buffer {
  return Buffer.from('0001', 'ascii');
}
interface PktLine { kind: 'data' | 'flush' | 'delim' | 'end'; data: Buffer; }
function parsePktLines(buf: Buffer): { lines: PktLine[]; rest: Buffer } {
  const lines: PktLine[] = [];
  let off = 0;
  while (off + 4 <= buf.length) {
    const len = parseInt(buf.toString('ascii', off, off + 4), 16);
    if (Number.isNaN(len)) throw new Error('bad pkt-line length');
    if (len === 0) { lines.push({ kind: 'flush', data: Buffer.alloc(0) }); off += 4; continue; }
    if (len === 1) { lines.push({ kind: 'delim', data: Buffer.alloc(0) }); off += 4; continue; }
    if (len === 2) { lines.push({ kind: 'end', data: Buffer.alloc(0) }); off += 4; continue; }
    if (len < 4 || off + len > buf.length) throw new Error('truncated pkt-line');
    lines.push({ kind: 'data', data: buf.subarray(off + 4, off + len) });
    off += len;
  }
  return { lines, rest: buf.subarray(off) };
}

// ---------------------------------------------------------------- git objects
type ObjType = 'commit' | 'tree' | 'blob' | 'tag';
interface GitObj { type: ObjType; data: Buffer; }
const objects = new Map<string, GitObj>(); // global object store, shared by all repos

function hashObject(type: ObjType, data: Buffer): string {
  const h = createHash('sha1');
  h.update(`${type} ${data.length}\0`);
  h.update(data);
  return h.digest('hex');
}
function storeObject(type: ObjType, data: Buffer): string {
  const oid = hashObject(type, data);
  if (!objects.has(oid)) objects.set(oid, { type, data });
  return oid;
}
interface TreeEntry { mode: string; name: string; oid: string; }
function parseTree(data: Buffer): TreeEntry[] {
  const entries: TreeEntry[] = [];
  let off = 0;
  while (off < data.length) {
    const sp = data.indexOf(0x20, off);
    const nul = data.indexOf(0, sp);
    const mode = data.toString('ascii', off, sp);
    const name = data.toString('utf8', sp + 1, nul);
    const oid = data.subarray(nul + 1, nul + 21).toString('hex');
    entries.push({ mode, name, oid });
    off = nul + 21;
  }
  return entries;
}
function buildTree(entries: TreeEntry[]): Buffer {
  const sorted = [...entries].sort((a, b) => {
    const ka = a.mode === '40000' ? `${a.name}/` : a.name;
    const kb = b.mode === '40000' ? `${b.name}/` : b.name;
    return ka < kb ? -1 : ka > kb ? 1 : 0;
  });
  const parts: Buffer[] = [];
  for (const e of sorted) {
    parts.push(Buffer.from(`${e.mode} ${e.name}\0`, 'utf8'));
    parts.push(Buffer.from(e.oid, 'hex'));
  }
  return Buffer.concat(parts);
}
interface CommitView { tree: string; parents: string[]; author: string; committer: string; message: string; }
// Commits are immutable, so parsed views are cached by oid.
const commitCache = new Map<string, CommitView>();
function parseCommitCached(oid: string): CommitView | null {
  const hit = commitCache.get(oid);
  if (hit) return hit;
  const obj = objects.get(oid);
  if (!obj || obj.type !== 'commit') return null;
  const cv = parseCommit(obj.data);
  if (commitCache.size > 8192) commitCache.clear();
  commitCache.set(oid, cv);
  return cv;
}
function parseCommit(data: Buffer): CommitView {
  const text = data.toString('utf8');
  const headEnd = text.indexOf('\n\n');
  const head = headEnd >= 0 ? text.slice(0, headEnd) : text;
  const message = headEnd >= 0 ? text.slice(headEnd + 2) : '';
  let tree = '';
  const parents: string[] = [];
  let author = '';
  let committer = '';
  for (const line of head.split('\n')) {
    if (line.startsWith('tree ')) tree = line.slice(5).trim();
    else if (line.startsWith('parent ')) parents.push(line.slice(7).trim());
    else if (line.startsWith('author ')) author = line.slice(7);
    else if (line.startsWith('committer ')) committer = line.slice(10);
  }
  return { tree, parents, author, committer, message };
}
function buildCommit(tree: string, parents: string[], message: string, epochSec: number, name = 'Conformance', email = 'conformance@make.fun'): Buffer {
  const ident = `${name} <${email}> ${epochSec} +0000`;
  let s = `tree ${tree}\n`;
  for (const p of parents) s += `parent ${p}\n`;
  s += `author ${ident}\ncommitter ${ident}\n\n${message}`;
  return Buffer.from(s, 'utf8');
}
function epochNow(): number {
  return Math.floor(Date.now() / 1000);
}
function reachableCommits(tips: string[]): Set<string> {
  const seen = new Set<string>();
  const queue = [...tips];
  let qi = 0;
  while (qi < queue.length) {
    const cur = queue[qi++]!;
    if (seen.has(cur)) continue;
    const cv = parseCommitCached(cur);
    if (!cv) continue;
    seen.add(cur);
    for (const p of cv.parents) queue.push(p);
  }
  return seen;
}
// Objects reachable from tips. With maxDepth >= 0 only commits within that
// many generations of a tip are included (plus their trees/blobs). Parent
// traversal stops at oids in stopAt (the client's shallow boundaries).
function reachableObjects(tips: string[], maxDepth = -1, stopAt: Set<string> = new Set()): Set<string> {
  const out = new Set<string>();
  const commits = new Set<string>();
  const queue: Array<{ oid: string; depth: number }> = tips.map((oid) => ({ oid, depth: 0 }));
  const seenCommit = new Set<string>();
  let qi = 0;
  while (qi < queue.length) {
    const cur = queue[qi++]!;
    if (seenCommit.has(cur.oid)) continue;
    const obj = objects.get(cur.oid);
    if (!obj) continue;
    if (obj.type === 'commit') {
      seenCommit.add(cur.oid);
      commits.add(cur.oid);
      out.add(cur.oid);
      if (stopAt.has(cur.oid)) continue;
      if (maxDepth >= 0 && cur.depth >= maxDepth) continue;
      const cv = parseCommitCached(cur.oid);
      if (cv) for (const p of cv.parents) queue.push({ oid: p, depth: cur.depth + 1 });
    } else if (obj.type === 'tag') {
      out.add(cur.oid);
      const m = obj.data.toString('utf8').match(/^object ([0-9a-f]{40})$/m);
      if (m) queue.push({ oid: m[1]!, depth: cur.depth });
    } else {
      out.add(cur.oid);
    }
  }
  for (const c of commits) {
    const cv = parseCommitCached(c);
    if (!cv) continue;
    collectTree(cv.tree, out);
  }
  return out;
}
function collectTree(treeOid: string, out: Set<string>): void {
  if (out.has(treeOid)) return;
  const obj = objects.get(treeOid);
  if (!obj || obj.type !== 'tree') return;
  out.add(treeOid);
  for (const e of parseTree(obj.data)) {
    if (e.mode === '160000') continue;
    if (e.mode === '40000') collectTree(e.oid, out);
    else out.add(e.oid);
  }
}
function treeAt(oid: string): Map<string, string> {
  const out = new Map<string, string>();
  const walk = (treeOid: string, prefix: string): void => {
    const obj = objects.get(treeOid);
    if (!obj || obj.type !== 'tree') return;
    for (const e of parseTree(obj.data)) {
      const p = prefix ? `${prefix}/${e.name}` : e.name;
      if (e.mode === '40000') walk(e.oid, p);
      else if (e.mode !== '160000') out.set(p, e.oid);
    }
  };
  walk(oid, '');
  return out;
}
function getBlobAt(treeOid: string, path: string): string | null {
  const parts = path.split('/').filter((p) => p !== '');
  let cur = treeOid;
  for (let i = 0; i < parts.length; i += 1) {
    const obj = objects.get(cur);
    if (!obj || obj.type !== 'tree') return null;
    const e = parseTree(obj.data).find((x) => x.name === parts[i]);
    if (!e) return null;
    if (i === parts.length - 1) return e.mode === '40000' ? null : e.oid;
    cur = e.oid;
  }
  return null;
}
function setPathInTree(baseTree: string | null, path: string, blobOid: string | null): string {
  const parts = path.split('/').filter((p) => p !== '');
  const build = (treeOid: string | null, idx: number): string => {
    const entries: TreeEntry[] = treeOid ? parseTree(objects.get(treeOid)!.data) : [];
    const name = parts[idx]!;
    const rest = entries.filter((e) => e.name !== name);
    if (idx === parts.length - 1) {
      if (blobOid !== null) rest.push({ mode: '100644', name, oid: blobOid });
    } else {
      const child = entries.find((e) => e.name === name);
      const childTree = build(child && child.mode === '40000' ? child.oid : null, idx + 1);
      const childObj = objects.get(childTree);
      if (childObj && parseTree(childObj.data).length > 0) rest.push({ mode: '40000', name, oid: childTree });
    }
    return storeObject('tree', buildTree(rest));
  };
  return build(baseTree, 0);
}
function listDir(treeOid: string, path: string): TreeEntry[] | null {
  if (path === '' || path === '/') {
    const obj = objects.get(treeOid);
    return obj && obj.type === 'tree' ? parseTree(obj.data) : null;
  }
  const parts = path.split('/').filter((p) => p !== '');
  let cur = treeOid;
  for (const part of parts) {
    const obj = objects.get(cur);
    if (!obj || obj.type !== 'tree') return null;
    const e = parseTree(obj.data).find((x) => x.name === part);
    if (!e || e.mode !== '40000') return null;
    cur = e.oid;
  }
  const obj = objects.get(cur);
  return obj && obj.type === 'tree' ? parseTree(obj.data) : null;
}
function isAncestor(ancestor: string, descendant: string): boolean {
  if (ancestor === descendant) return true;
  const seen = new Set<string>();
  const queue = [descendant];
  let qi = 0;
  let steps = 0;
  while (qi < queue.length && steps < 20000) {
    const cur = queue[qi++]!;
    steps += 1;
    if (cur === ancestor) return true;
    if (seen.has(cur)) continue;
    seen.add(cur);
    const cv = parseCommitCached(cur);
    if (!cv) continue;
    for (const p of cv.parents) queue.push(p);
  }
  return false;
}
function mergeBase(a: string, b: string): string | null {
  const ancA = reachableCommits([a]);
  const queue = [b];
  const seen = new Set<string>();
  let qi = 0;
  while (qi < queue.length) {
    const cur = queue[qi++]!;
    if (seen.has(cur)) continue;
    seen.add(cur);
    if (ancA.has(cur)) return cur;
    const cv = parseCommitCached(cur);
    if (!cv) continue;
    for (const p of cv.parents) queue.push(p);
  }
  return null;
}
function diffTrees(baseTree: string | null, headTree: string | null): Array<{ path: string; oldOid: string | null; newOid: string | null }> {
  const b = baseTree ? treeAt(baseTree) : new Map<string, string>();
  const h = headTree ? treeAt(headTree) : new Map<string, string>();
  const paths = new Set([...b.keys(), ...h.keys()]);
  const out: Array<{ path: string; oldOid: string | null; newOid: string | null }> = [];
  for (const p of [...paths].sort()) {
    const o = b.get(p) ?? null;
    const n = h.get(p) ?? null;
    if (o !== n) out.push({ path: p, oldOid: o, newOid: n });
  }
  return out;
}
function countLines(buf: Buffer): number {
  if (buf.length === 0) return 0;
  const lines = buf.toString('utf8').split('\n');
  if (lines[lines.length - 1] === '') lines.pop();
  return lines.length;
}
function diffLineCounts(oldBuf: Buffer | null, newBuf: Buffer | null): { additions: number; deletions: number } {
  if (!oldBuf) return { additions: countLines(newBuf ?? Buffer.alloc(0)), deletions: 0 };
  if (!newBuf) return { additions: 0, deletions: countLines(oldBuf) };
  const a = oldBuf.toString('utf8').split('\n');
  const b = newBuf.toString('utf8').split('\n');
  if (a[a.length - 1] === '') a.pop();
  if (b[b.length - 1] === '') b.pop();
  const n = a.length;
  const m = b.length;
  const dp: number[][] = Array.from({ length: n + 1 }, () => new Array<number>(m + 1).fill(0));
  for (let i = n - 1; i >= 0; i -= 1) {
    for (let j = m - 1; j >= 0; j -= 1) {
      dp[i]![j] = a[i] === b[j] ? dp[i + 1]![j + 1]! + 1 : Math.max(dp[i + 1]![j]!, dp[i]![j + 1]!);
    }
  }
  const common = dp[0]![0]!;
  return { additions: m - common, deletions: n - common };
}
function applyDelta(base: Buffer, delta: Buffer): Buffer {
  let off = 0;
  const readVarint = (): number => {
    let v = 0;
    let shift = 0;
    for (;;) {
      const byte = delta[off++]!;
      v |= (byte & 0x7f) << shift;
      shift += 7;
      if ((byte & 0x80) === 0) break;
    }
    return v;
  };
  const srcSize = readVarint();
  const dstSize = readVarint();
  if (srcSize !== base.length) throw new Error('delta base size mismatch');
  const out: Buffer[] = [];
  while (off < delta.length) {
    const op = delta[off++]!;
    if (op & 0x80) {
      let cpOff = 0;
      let cpSize = 0;
      if (op & 0x01) cpOff = delta[off++]!;
      if (op & 0x02) cpOff |= delta[off++]! << 8;
      if (op & 0x04) cpOff |= delta[off++]! << 16;
      if (op & 0x08) cpOff |= delta[off++]! << 24;
      if (op & 0x10) cpSize = delta[off++]!;
      if (op & 0x20) cpSize |= delta[off++]! << 8;
      if (op & 0x40) cpSize |= delta[off++]! << 16;
      if (cpSize === 0) cpSize = 0x10000;
      out.push(base.subarray(cpOff, cpOff + cpSize));
    } else if (op !== 0) {
      out.push(delta.subarray(off, off + op));
      off += op;
    } else {
      throw new Error('delta opcode 0');
    }
  }
  const result = Buffer.concat(out);
  if (result.length !== dstSize) throw new Error('delta size mismatch');
  return result;
}
function adler32(data: Buffer): number {
  let a = 1;
  let b = 0;
  for (let i = 0; i < data.length; i += 1) {
    a = (a + data[i]!) % 65521;
    b = (b + a) % 65521;
  }
  return ((b << 16) | a) >>> 0;
}
// inflateSync ignores trailing bytes and throws on truncation. The fast path
// inflates once from `off` (the rest of the pack is trailing garbage to it),
// then locates the stream's end by its Adler-32 trailer; a binary search is
// kept as a fallback.
function inflateAt(buf: Buffer, off: number, expectedSize: number): { data: Buffer; next: number } {
  const data = inflateSync(buf.subarray(off));
  if (data.length !== expectedSize) throw new Error('pack object size mismatch');
  const adBuf = Buffer.alloc(4);
  adBuf.writeUInt32BE(adler32(data), 0);
  let idx = buf.indexOf(adBuf, off + 2);
  while (idx >= 0) {
    const len = idx + 4 - off;
    try {
      const out = inflateSync(buf.subarray(off, off + len));
      if (out.length === expectedSize) return { data: out, next: off + len };
    } catch { /* false-positive Adler match, keep scanning */ }
    idx = buf.indexOf(adBuf, idx + 1);
  }
  // Fallback: binary search for the smallest prefix that inflates exactly.
  const max = buf.length - off;
  let lo = 1;
  let hi = max;
  let found = -1;
  let foundData: Buffer = data;
  while (lo <= hi) {
    const mid = (lo + hi) >> 1;
    try {
      const out = inflateSync(buf.subarray(off, off + mid));
      if (out.length === expectedSize) { found = mid; foundData = out; hi = mid - 1; }
      else lo = mid + 1;
    } catch {
      lo = mid + 1;
    }
  }
  if (found < 0) throw new Error('cannot inflate pack object');
  return { data: foundData, next: off + found };
}
const TYPE_NUM_TO_NAME: Record<number, ObjType> = { 1: 'commit', 2: 'tree', 3: 'blob', 4: 'tag' };
const TYPE_NAME_TO_NUM: Record<ObjType, number> = { commit: 1, tree: 2, blob: 3, tag: 4 };
function readPack(pack: Buffer): Array<{ type: ObjType; data: Buffer; oid: string }> {
  if (pack.length < 12 || pack.toString('ascii', 0, 4) !== 'PACK') throw new Error('not a pack');
  const version = pack.readUInt32BE(4);
  if (version !== 2 && version !== 3) throw new Error('bad pack version');
  const count = pack.readUInt32BE(8);
  let off = 12;
  const byOffset = new Map<number, { type: ObjType; data: Buffer; oid: string }>();
  const results: Array<{ type: ObjType; data: Buffer; oid: string }> = [];
  for (let i = 0; i < count; i += 1) {
    const start = off;
    let byte = pack[off++]!;
    const typeNum = (byte >> 4) & 0x7;
    let size = byte & 0x0f;
    let shift = 4;
    while (byte & 0x80) {
      byte = pack[off++]!;
      size |= (byte & 0x7f) << shift;
      shift += 7;
    }
    let baseOff: number | undefined;
    let baseOid: string | undefined;
    if (typeNum === 6) {
      byte = pack[off++]!;
      let bOff = byte & 0x7f;
      while (byte & 0x80) {
        byte = pack[off++]!;
        bOff = ((bOff + 1) << 7) | (byte & 0x7f);
      }
      baseOff = start - bOff;
    } else if (typeNum === 7) {
      baseOid = pack.subarray(off, off + 20).toString('hex');
      off += 20;
    }
    const inflated = inflateAt(pack, off, size);
    off = inflated.next;
    let type: ObjType;
    let data: Buffer;
    if (typeNum === 6 || typeNum === 7) {
      const base = typeNum === 6 ? byOffset.get(baseOff!) : results.find((r) => r.oid === baseOid) ?? byOffset.get(0);
      const baseEntry = typeNum === 6 ? byOffset.get(baseOff!) : [...byOffset.values()].find((r) => r.oid === baseOid);
      if (!baseEntry && !base) throw new Error('delta base missing');
      const b = baseEntry ?? base!;
      data = applyDelta(b.data, inflated.data);
      type = b.type;
    } else {
      type = TYPE_NUM_TO_NAME[typeNum]!;
      if (!type) throw new Error(`unknown pack object type ${typeNum}`);
      data = inflated.data;
    }
    const oid = hashObject(type, data);
    const entry = { type, data, oid };
    byOffset.set(start, entry);
    results.push(entry);
  }
  return results;
}
function writePack(oids: string[]): Buffer {
  const present = oids.filter((oid) => objects.has(oid));
  const header = Buffer.alloc(12);
  header.write('PACK', 0, 'ascii');
  header.writeUInt32BE(2, 4);
  header.writeUInt32BE(present.length, 8);
  const parts: Buffer[] = [header];
  for (const oid of present) {
    const obj = objects.get(oid)!;
    const typeNum = TYPE_NAME_TO_NUM[obj.type];
    const size = obj.data.length;
    const head: number[] = [];
    let b = (typeNum << 4) | (size & 0x0f);
    let rest = size >> 4;
    if (rest > 0) b |= 0x80;
    head.push(b);
    while (rest > 0) {
      b = rest & 0x7f;
      rest >>= 7;
      if (rest > 0) b |= 0x80;
      head.push(b);
    }
    parts.push(Buffer.from(head));
    parts.push(deflateSync(obj.data, { level: 1 }));
  }
  const body = Buffer.concat(parts);
  return Buffer.concat([body, sha1buf(body)]);
}
function sidebandPack(pack: Buffer): Buffer {
  const chunks: Buffer[] = [];
  for (let off = 0; off < pack.length; off += 32768) {
    const slice = pack.subarray(off, Math.min(pack.length, off + 32768));
    chunks.push(pkt(Buffer.concat([Buffer.from([1]), slice])));
  }
  if (pack.length === 0) chunks.push(pkt(Buffer.from([1])));
  return Buffer.concat(chunks);
}

// ---------------------------------------------------------------- store
interface Label { name: string; color: string; }
interface Comment { id: number; body: string; created_at: string; }
interface Issue {
  id: number; number: number; title: string; body: string; state: 'open' | 'closed';
  labels: Label[]; comments: Comment[]; seq: number; created_at: string; updated_at: string;
  jsonCache: string | null;
}
interface Pull {
  id: number; number: number; title: string; body: string; state: 'open' | 'closed';
  merged: boolean; headRef: string; baseRef: string; headSha: string; baseSha: string;
  mergeSha: string | null; merged_at: string | null; seq: number; created_at: string; updated_at: string;
}
interface Repo {
  id: number; name: string; owner: string; private: boolean; description: string;
  default_branch: string; created_at: string; updated_at: string;
  refs: Map<string, string>; labels: Map<string, Label>;
  issues: Issue[]; pulls: Pull[]; issueSeq: number; prSeq: number; commentSeq: number;
}
const repos = new Map<string, Repo>(); // key `${owner}/${name}`
let repoIdSeq = 5000;
let globalIdSeq = 1;
function repoKey(owner: string, name: string): string {
  return `${owner}/${name}`;
}
function newRepo(owner: string, name: string, isPrivate: boolean, description: string): Repo {
  const now = nowIso();
  const repo: Repo = {
    id: repoIdSeq++, name, owner, private: isPrivate, description,
    default_branch: 'main', created_at: now, updated_at: now,
    refs: new Map(), labels: new Map(), issues: [], pulls: [],
    issueSeq: 0, prSeq: 0, commentSeq: 0,
  };
  repos.set(repoKey(owner, name), repo);
  return repo;
}
function repoGid(r: Repo): string {
  return gid('R', repoKey(r.owner, r.name));
}
function issueGid(r: Repo, iss: Issue): string {
  return gid('I', `${repoKey(r.owner, r.name)}#${iss.number}`);
}
function pullGid(r: Repo, pr: Pull): string {
  return gid('PR', `${repoKey(r.owner, r.name)}#${pr.number}`);
}
function commentGid(r: Repo, iss: Issue, c: Comment): string {
  return gid('C', `${repoKey(r.owner, r.name)}#${iss.number}:${c.id}`);
}
function resolveRef(repo: Repo, ref: string): string | undefined {
  if (ref.startsWith('refs/')) return repo.refs.get(ref);
  return repo.refs.get(`refs/heads/${ref}`);
}
function refTip(repo: Repo, branch: string): string | undefined {
  return resolveRef(repo, branch);
}
function repoJson(r: Repo): Record<string, unknown> {
  return {
    id: r.id, node_id: repoGid(r), name: r.name, full_name: repoKey(r.owner, r.name),
    owner: { login: r.owner, id: r.owner === VIEWER_LOGIN ? VIEWER_ID : 1002, type: 'User' },
    private: r.private, description: r.description, default_branch: r.default_branch,
    created_at: r.created_at, updated_at: r.updated_at, pushed_at: r.updated_at,
    html_url: `https://example.invalid/${r.owner}/${r.name}`,
    url: `/api/v3/repos/${r.owner}/${r.name}`,
    clone_url: `https://example.invalid/${r.owner}/${r.name}.git`,
    git_url: `git://example.invalid/${r.owner}/${r.name}.git`,
    ssh_url: `git@example.invalid:${r.owner}/${r.name}.git`,
    has_issues: true, has_projects: true, has_wiki: true, has_pages: false,
    has_downloads: true, archived: false, disabled: false, fork: false,
    open_issues_count: r.issues.filter((i) => i.state === 'open').length,
    license: null, topics: [], visibility: r.private ? 'private' : 'public',
    permissions: { admin: true, maintain: true, push: true, triage: true, pull: true },
  };
}
function issueJson(r: Repo, iss: Issue): Record<string, unknown> {
  return {
    id: iss.id, node_id: issueGid(r, iss), number: iss.number, title: iss.title,
    body: iss.body, state: iss.state,
    user: { login: VIEWER_LOGIN, id: VIEWER_ID, type: 'User' },
    labels: iss.labels.map((l) => ({ name: l.name, color: l.color })),
    comments: iss.comments.length, created_at: iss.created_at, updated_at: iss.updated_at,
    closed_at: iss.state === 'closed' ? iss.updated_at : null,
    html_url: `https://example.invalid/${r.owner}/${r.name}/issues/${iss.number}`,
    url: `/api/v3/repos/${r.owner}/${r.name}/issues/${iss.number}`,
    repository_url: `/api/v3/repos/${r.owner}/${r.name}`,
    assignee: null, assignees: [], milestone: null, locked: false,
    author_association: 'OWNER',
  };
}
function pullJson(r: Repo, pr: Pull): Record<string, unknown> {
  const headSha = refTip(r, pr.headRef) ?? pr.headSha;
  const baseSha = refTip(r, pr.baseRef) ?? pr.baseSha;
  return {
    id: pr.id, node_id: pullGid(r, pr), number: pr.number, title: pr.title, body: pr.body,
    state: pr.state, merged: pr.merged, mergeable: pr.merged ? true : isMergeable(r, pr),
    merged_at: pr.merged_at, merge_commit_sha: pr.mergeSha,
    head: { label: `${r.owner}:${pr.headRef}`, ref: pr.headRef, sha: headSha, repo: repoJson(r), user: { login: VIEWER_LOGIN, id: VIEWER_ID } },
    base: { label: `${r.owner}:${pr.baseRef}`, ref: pr.baseRef, sha: baseSha, repo: repoJson(r), user: { login: VIEWER_LOGIN, id: VIEWER_ID } },
    user: { login: VIEWER_LOGIN, id: VIEWER_ID, type: 'User' },
    created_at: pr.created_at, updated_at: pr.updated_at, closed_at: pr.state === 'closed' ? pr.updated_at : null,
    html_url: `https://example.invalid/${r.owner}/${r.name}/pull/${pr.number}`,
    url: `/api/v3/repos/${r.owner}/${r.name}/pulls/${pr.number}`,
    comments: 0, review_comments: 0, commits: 1, additions: 0, deletions: 0, changed_files: 0,
    draft: false, locked: false, maintainer_can_modify: false, rebaseable: true,
  };
}
function isMergeable(r: Repo, pr: Pull): boolean {
  return !prConflict(r, pr);
}
function prBaseTip(r: Repo, pr: Pull): string | undefined {
  return refTip(r, pr.baseRef);
}
function prHeadTip(r: Repo, pr: Pull): string | undefined {
  return refTip(r, pr.headRef);
}
// A PR conflicts when a file it changes was also changed on the base branch
// since the merge-base, to a different value.
function prConflict(r: Repo, pr: Pull): boolean {
  const head = prHeadTip(r, pr);
  const base = prBaseTip(r, pr);
  if (!head || !base) return false;
  const mb = mergeBase(head, base);
  const mbTree = mb ? parseCommit(objects.get(mb)!.data).tree : null;
  const headTree = parseCommit(objects.get(head)!.data).tree;
  const baseTree = parseCommit(objects.get(base)!.data).tree;
  const mbMap = mbTree ? treeAt(mbTree) : new Map<string, string>();
  const headMap = treeAt(headTree);
  const baseMap = treeAt(baseTree);
  for (const [p, hOid] of headMap) {
    const mbOid = mbMap.get(p) ?? null;
    const bOid = baseMap.get(p) ?? null;
    if (hOid !== mbOid && bOid !== mbOid && hOid !== bOid) return true;
  }
  for (const [p, mbOid] of mbMap) {
    if (!headMap.has(p) && baseMap.get(p) !== mbOid && baseMap.has(p)) return true;
    if (!headMap.has(p) && !baseMap.has(p)) continue;
  }
  return false;
}
function prFiles(r: Repo, pr: Pull): Array<Record<string, unknown>> {
  const head = prHeadTip(r, pr);
  const base = prBaseTip(r, pr);
  if (!head || !base) return [];
  const mb = mergeBase(head, base);
  const mbTree = mb ? parseCommit(objects.get(mb)!.data).tree : null;
  const headTree = parseCommit(objects.get(head)!.data).tree;
  const changes = diffTrees(mbTree, headTree);
  return changes.map((c) => {
    const oldBuf = c.oldOid ? objects.get(c.oldOid)?.data ?? null : null;
    const newBuf = c.newOid ? objects.get(c.newOid)?.data ?? null : null;
    const counts = diffLineCounts(oldBuf, newBuf);
    const status = c.oldOid === null ? 'added' : c.newOid === null ? 'removed' : 'modified';
    return {
      sha: c.newOid ?? c.oldOid, filename: c.path, status,
      additions: counts.additions, deletions: counts.deletions,
      changes: counts.additions + counts.deletions,
      blob_url: '', raw_url: '', contents_url: '',
    };
  });
}
// Squash-merge: one commit on the base branch whose tree is the 3-way merge
// of base tip + head changes; returns the new commit oid.
function squashMerge(r: Repo, pr: Pull): string {
  const head = prHeadTip(r, pr)!;
  const base = prBaseTip(r, pr)!;
  const mb = mergeBase(head, base);
  const mbTree = mb ? parseCommit(objects.get(mb)!.data).tree : null;
  const headTree = parseCommit(objects.get(head)!.data).tree;
  const baseTree = parseCommit(objects.get(base)!.data).tree;
  let mergedTree = baseTree;
  for (const c of diffTrees(mbTree, headTree)) {
    mergedTree = setPathInTree(mergedTree, c.path, c.newOid);
  }
  const msg = `${pr.title} (#${pr.number})\n`;
  const commit = buildCommit(mergedTree, [base], msg, epochNow(), VIEWER_LOGIN, VIEWER_EMAIL);
  const oid = storeObject('commit', commit);
  r.refs.set(`refs/heads/${pr.baseRef}`, oid);
  return oid;
}

// ---------------------------------------------------------------- HTTP helpers
function sendJsonText(res: ServerResponse, status: number, text: string, extra: Record<string, string> = {}): void {
  res.writeHead(status, {
    'content-type': JSON_TYPE,
    'x-github-request-id': `req-${(++reqCounter).toString(36)}-${Date.now().toString(36)}`,
    'content-length': Buffer.byteLength(text),
    ...extra,
  });
  res.end(text);
}
function sendJson(res: ServerResponse, status: number, body: unknown, extra: Record<string, string> = {}): void {
  const text = status === 204 ? '' : `${JSON.stringify(body)}\n`;
  res.writeHead(status, {
    'content-type': JSON_TYPE,
    'x-github-request-id': `req-${(++reqCounter).toString(36)}-${Date.now().toString(36)}`,
    ...(status === 204 ? {} : { 'content-length': Buffer.byteLength(text) }),
    ...extra,
  });
  res.end(text);
}
function sendErr(res: ServerResponse, status: number, message: string, extra: Record<string, string> = {}): void {
  sendJson(res, status, { message, documentation_url: 'https://example.invalid/docs' }, extra);
}
function readBody(req: IncomingMessage): Promise<Buffer> {
  return new Promise<Buffer>((resolve, reject) => {
    const chunks: Buffer[] = [];
    let total = 0;
    req.on('data', (c: Buffer) => {
      total += c.length;
      if (total > 64 * 1024 * 1024) { reject(new Error('body too large')); req.destroy(); return; }
      chunks.push(c);
    });
    req.on('end', () => resolve(Buffer.concat(chunks)));
    req.on('error', reject);
  });
}
function parseJsonBody(buf: Buffer): { ok: true; value: unknown } | { ok: false } {
  if (buf.length === 0) return { ok: true, value: {} };
  try {
    return { ok: true, value: JSON.parse(buf.toString('utf8')) };
  } catch {
    return { ok: false };
  }
}
function pathOf(req: IncomingMessage): string {
  try {
    return decodeURIComponent(new URL(req.url ?? '/', 'http://entry').pathname);
  } catch {
    return '/';
  }
}
function queryOf(req: IncomingMessage): URLSearchParams {
  try {
    return new URL(req.url ?? '/', 'http://entry').searchParams;
  } catch {
    return new URLSearchParams();
  }
}
function bearerToken(req: IncomingMessage): string | null {
  const h = req.headers.authorization;
  if (!h || !h.startsWith('Bearer ')) return null;
  return h.slice(7).trim() || null;
}
// The viewer login for this request: the shop token names adaiversen; any
// other bearer token is a foreign user (its repos are a different namespace).
function viewerLogin(req: IncomingMessage): string | null {
  const tok = bearerToken(req);
  if (tok === null) return null;
  const shop = process.env.MAKEFUN_SHOP_TOKEN;
  if (shop && tok !== shop) return 'foreign-user';
  return VIEWER_LOGIN;
}
function requireAuth(req: IncomingMessage, res: ServerResponse): string | null {
  const login = viewerLogin(req);
  if (login === null) { sendErr(res, 401, 'Requires authentication'); return null; }
  return login;
}
function originOf(req: IncomingMessage): string {
  const host = req.headers.host ?? 'localhost';
  return `http://${host}`;
}

// ---------------------------------------------------------------- REST v3
function findRepo(owner: string, name: string, login: string): Repo | null {
  if (owner !== login) return null;
  return repos.get(repoKey(owner, name)) ?? null;
}
function paginate<T>(items: T[], q: URLSearchParams): { page: T[]; totalPages: number; pageNum: number; perPage: number } {
  const perPage = Math.max(1, Math.min(100, Number(q.get('per_page') ?? '30') || 30));
  const pageNum = Math.max(1, Number(q.get('page') ?? '1') || 1);
  const start = (pageNum - 1) * perPage;
  return { page: items.slice(start, start + perPage), totalPages: Math.max(1, Math.ceil(items.length / perPage)), pageNum, perPage };
}
function linkHeader(req: IncomingMessage, q: URLSearchParams, pageNum: number, totalPages: number, perPage: number): string {
  const base = `${originOf(req)}${pathOf(req)}`;
  const params = new URLSearchParams(q);
  params.set('per_page', String(perPage));
  const links: string[] = [];
  if (pageNum < totalPages) {
    params.set('page', String(pageNum + 1));
    links.push(`<${base}?${params.toString()}>; rel="next"`);
  }
  if (pageNum > 1) {
    params.set('page', String(pageNum - 1));
    links.push(`<${base}?${params.toString()}>; rel="prev"`);
  }
  params.set('page', String(totalPages));
  links.push(`<${base}?${params.toString()}>; rel="last"`);
  params.set('page', '1');
  links.push(`<${base}?${params.toString()}>; rel="first"`);
  return links.join(', ');
}
async function handleRest(req: IncomingMessage, res: ServerResponse): Promise<boolean> {
  const path = pathOf(req);
  const method = req.method ?? 'GET';
  if (!path.startsWith('/api/v3')) return false;
  const sub = path.slice('/api/v3'.length) || '/';
  const q = queryOf(req);

  if (method === 'GET' && (sub === '/' || sub === '')) {
    sendJson(res, 200, { current_user_url: '/api/v3/user', rate_limit_url: '/api/v3/rate_limit' }, { 'x-oauth-scopes': 'repo, read:org' });
    return true;
  }
  if (method === 'GET' && sub === '/meta') {
    sendJson(res, 200, { installed_version: '1.0.0', verifiable_password_authentication: true, git: ['1.0.0'], github_services: true });
    return true;
  }
  // All other /api/v3 routes require auth.
  const login = requireAuth(req, res);
  if (login === null) return true;

  const readJson = async (): Promise<unknown | null> => {
    const buf = await readBody(req);
    const parsed = parseJsonBody(buf);
    if (!parsed.ok) { sendErr(res, 400, 'Problems parsing JSON'); return null; }
    return parsed.value;
  };

  if (method === 'GET' && sub === '/user') {
    sendJson(res, 200, { login, id: login === VIEWER_LOGIN ? VIEWER_ID : 9999, type: 'User', name: login });
    return true;
  }
  if (sub === '/user/repos') {
    if (method === 'GET') {
      const mine = [...repos.values()].filter((r) => r.owner === login).sort((a, b) => a.id - b.id);
      const { page, totalPages, pageNum, perPage } = paginate(mine, q);
      const extra: Record<string, string> = {};
      if (totalPages > 1) extra.link = linkHeader(req, q, pageNum, totalPages, perPage);
      sendJson(res, 200, page.map(repoJson), extra);
      return true;
    }
    if (method === 'POST') {
      const body = await readJson();
      if (body === null) return true;
      const b = (body ?? {}) as Record<string, unknown>;
      const name = typeof b.name === 'string' ? b.name : '';
      if (!name) { sendErr(res, 422, 'name is required'); return true; }
      if (repos.has(repoKey(login, name))) { sendErr(res, 422, 'Repository already exists'); return true; }
      const repo = newRepo(login, name, b.private === true, typeof b.description === 'string' ? b.description : '');
      if (typeof b.default_branch === 'string' && b.default_branch) repo.default_branch = b.default_branch;
      sendJson(res, 201, repoJson(repo));
      return true;
    }
  }

  const m = sub.match(/^\/repos\/([^/]+)\/([^/]+)(.*)$/);
  if (m) {
    const owner = decodeURIComponent(m[1]!);
    const name = decodeURIComponent(m[2]!);
    const rest = m[3] ?? '';
    const repo = findRepo(owner, name, login);
    if (!repo) { sendErr(res, 404, 'Not Found'); return true; }

    if (rest === '' || rest === '/') {
      if (method === 'GET') { sendJson(res, 200, repoJson(repo)); return true; }
      if (method === 'PATCH') {
        const body = await readJson();
        if (body === null) return true;
        const b = (body ?? {}) as Record<string, unknown>;
        if (typeof b.description === 'string') repo.description = b.description;
        if (typeof b.default_branch === 'string' && b.default_branch) repo.default_branch = b.default_branch;
        repo.updated_at = nowIso();
        sendJson(res, 200, repoJson(repo));
        return true;
      }
      if (method === 'DELETE') {
        repos.delete(repoKey(owner, name));
        sendJson(res, 204, null);
        return true;
      }
    }
    if (rest === '/branches' && method === 'GET') {
      const out = [...repo.refs.entries()]
        .filter(([r]) => r.startsWith('refs/heads/'))
        .map(([r, sha]) => ({ name: r.slice('refs/heads/'.length), commit: { sha }, protected: false }));
      sendJson(res, 200, out);
      return true;
    }
    const branchOne = rest.match(/^\/branches\/([^/]+)$/);
    if (branchOne && method === 'GET') {
      const sha = repo.refs.get(`refs/heads/${decodeURIComponent(branchOne[1]!)}`);
      if (!sha) { sendErr(res, 404, 'Not Found'); return true; }
      sendJson(res, 200, { name: decodeURIComponent(branchOne[1]!), commit: { sha }, protected: false });
      return true;
    }
    if (rest === '/commits' && method === 'GET') {
      const shaParam = q.get('sha');
      const tip = shaParam ? resolveRef(repo, shaParam) : repo.refs.get(`refs/heads/${repo.default_branch}`);
      const out: Array<Record<string, unknown>> = [];
      if (tip) {
        const seen = new Set<string>();
        const queue = [tip];
        while (queue.length > 0 && out.length < 1000) {
          const cur = queue.shift()!;
          if (seen.has(cur)) continue;
          seen.add(cur);
          const obj = objects.get(cur);
          if (!obj || obj.type !== 'commit') continue;
          const cv = parseCommit(obj.data);
          out.push({ sha: cur, commit: { message: cv.message, author: { name: 'Conformance', email: 'conformance@make.fun' }, committer: { name: 'Conformance', email: 'conformance@make.fun' } }, parents: cv.parents.map((p) => ({ sha: p })) });
          for (const p of cv.parents) queue.push(p);
        }
      }
      sendJson(res, 200, out);
      return true;
    }
    if (rest === '/git/refs' && method === 'POST') {
      const body = await readJson();
      if (body === null) return true;
      const b = (body ?? {}) as Record<string, unknown>;
      const ref = typeof b.ref === 'string' ? b.ref : '';
      const sha = typeof b.sha === 'string' ? b.sha : '';
      if (!ref || !sha) { sendErr(res, 422, 'ref and sha are required'); return true; }
      if (repo.refs.has(ref)) { sendErr(res, 422, 'Reference already exists'); return true; }
      if (!objects.has(sha)) { sendErr(res, 422, 'Object does not exist'); return true; }
      repo.refs.set(ref, sha);
      sendJson(res, 201, { ref, node_id: gid('REF', `${repoKey(owner, name)}:${ref}`), url: `/api/v3/repos/${owner}/${name}/git/refs/${encodeURIComponent(ref)}`, object: { sha, type: objects.get(sha)?.type ?? 'commit', url: '' } });
      return true;
    }
    const gitRefOne = rest.match(/^\/git\/refs\/(.+)$/);
    if (gitRefOne && method === 'GET') {
      const ref = decodeURIComponent(gitRefOne[1]!);
      const full = ref.startsWith('refs/') ? ref : `refs/heads/${ref}`;
      const sha = repo.refs.get(full);
      if (!sha) { sendErr(res, 404, 'Not Found'); return true; }
      sendJson(res, 200, { ref: full, node_id: gid('REF', `${repoKey(owner, name)}:${full}`), object: { sha, type: objects.get(sha)?.type ?? 'commit', url: '' } });
      return true;
    }
    if (rest === '/labels' && method === 'POST') {
      const body = await readJson();
      if (body === null) return true;
      const b = (body ?? {}) as Record<string, unknown>;
      const lname = typeof b.name === 'string' ? b.name : '';
      if (!lname) { sendErr(res, 422, 'name is required'); return true; }
      const label: Label = { name: lname, color: typeof b.color === 'string' ? b.color : 'ededed' };
      repo.labels.set(lname, label);
      sendJson(res, 201, { name: label.name, color: label.color, id: globalIdSeq++, node_id: gid('L', `${repoKey(owner, name)}:${lname}`), url: '', default: false, description: '' });
      return true;
    }
    if (rest === '/labels' && method === 'GET') {
      sendJson(res, 200, [...repo.labels.values()].map((l) => ({ name: l.name, color: l.color })));
      return true;
    }
    // Contents
    const contentsM = rest.match(/^\/contents\/(.+)$/);
    if (contentsM) {
      const cpath = decodeURIComponent(contentsM[1]!);
      if (method === 'GET') {
        const refParam = q.get('ref');
        const tip = refParam ? resolveRef(repo, refParam) : repo.refs.get(`refs/heads/${repo.default_branch}`);
        if (!tip) { sendErr(res, 404, 'Not Found'); return true; }
        const tree = parseCommit(objects.get(tip)!.data).tree;
        const blobOid = getBlobAt(tree, cpath);
        if (blobOid) {
          const data = objects.get(blobOid)!.data;
          sendJson(res, 200, { type: 'file', encoding: 'base64', size: data.length, name: cpath.split('/').pop(), path: cpath, content: data.toString('base64'), sha: blobOid, url: '', html_url: '', download_url: '' });
          return true;
        }
        const dir = listDir(tree, cpath);
        if (dir) {
          sendJson(res, 200, dir.map((e) => ({ type: e.mode === '40000' ? 'dir' : 'file', name: e.name, path: `${cpath}/${e.name}`, sha: e.oid, size: e.mode === '40000' ? 0 : (objects.get(e.oid)?.data.length ?? 0), url: '', html_url: '', download_url: '' })));
          return true;
        }
        sendErr(res, 404, 'Not Found');
        return true;
      }
      if (method === 'PUT') {
        const body = await readJson();
        if (body === null) return true;
        const b = (body ?? {}) as Record<string, unknown>;
        const contentB64 = typeof b.content === 'string' ? b.content : '';
        const branch = typeof b.branch === 'string' ? b.branch : repo.default_branch;
        const refName = `refs/heads/${branch}`;
        const tip = repo.refs.get(refName);
        const isUpdate = !!tip;
        let curBlob: string | null = null;
        let curTree: string | null = null;
        if (tip) {
          curTree = parseCommit(objects.get(tip)!.data).tree;
          curBlob = getBlobAt(curTree, cpath);
        }
        if (typeof b.sha === 'string' && b.sha !== '' && curBlob !== null && b.sha !== curBlob) {
          sendErr(res, 409, 'sha does not match');
          return true;
        }
        const existed = curBlob !== null;
        const bytes = Buffer.from(contentB64, 'base64');
        const blobOid = storeObject('blob', bytes);
        const newTree = setPathInTree(curTree, cpath, blobOid);
        const msg = typeof b.message === 'string' ? b.message : `Update ${cpath}`;
        const commit = buildCommit(newTree, tip ? [tip] : [], msg, epochNow(), VIEWER_LOGIN, VIEWER_EMAIL);
        const commitOid = storeObject('commit', commit);
        repo.refs.set(refName, commitOid);
        repo.updated_at = nowIso();
        sendJson(res, existed ? 200 : 201, { content: { name: cpath.split('/').pop(), path: cpath, sha: blobOid, size: bytes.length, type: 'file', encoding: 'base64', content: contentB64 }, commit: { sha: commitOid, message: msg } });
        return true;
      }
      if (method === 'DELETE') {
        const body = await readJson();
        if (body === null) return true;
        const b = (body ?? {}) as Record<string, unknown>;
        const branch = typeof b.branch === 'string' ? b.branch : repo.default_branch;
        const refName = `refs/heads/${branch}`;
        const tip = repo.refs.get(refName);
        if (!tip) { sendErr(res, 404, 'Not Found'); return true; }
        const tree = parseCommit(objects.get(tip)!.data).tree;
        const curBlob = getBlobAt(tree, cpath);
        if (!curBlob) { sendErr(res, 404, 'Not Found'); return true; }
        if (typeof b.sha === 'string' && b.sha !== '' && b.sha !== curBlob) { sendErr(res, 409, 'sha does not match'); return true; }
        const newTree = setPathInTree(tree, cpath, null);
        const msg = typeof b.message === 'string' ? b.message : `Delete ${cpath}`;
        const commit = buildCommit(newTree, [tip], msg, epochNow(), VIEWER_LOGIN, VIEWER_EMAIL);
        const commitOid = storeObject('commit', commit);
        repo.refs.set(refName, commitOid);
        sendJson(res, 200, { commit: { sha: commitOid, message: msg } });
        return true;
      }
    }
    // Issues
    if (rest === '/issues' && method === 'POST') {
      const body = await readJson();
      if (body === null) return true;
      const b = (body ?? {}) as Record<string, unknown>;
      const title = typeof b.title === 'string' ? b.title : '';
      if (!title) { sendErr(res, 422, 'title is required'); return true; }
      const labelNames: string[] = Array.isArray(b.labels)
        ? (b.labels as unknown[]).map((l) => (typeof l === 'string' ? l : (l as Record<string, unknown>).name as string)).filter(Boolean)
        : [];
      for (const ln of labelNames) {
        if (!repo.labels.has(ln)) { sendErr(res, 422, `Label does not exist: ${ln}`); return true; }
      }
      repo.issueSeq += 1;
      const now = nowIso();
      const iss: Issue = {
        id: globalIdSeq++, number: repo.issueSeq, title, body: typeof b.body === 'string' ? b.body : '',
        state: 'open', labels: labelNames.map((n) => repo.labels.get(n)!), comments: [],
        seq: repo.issueSeq, created_at: now, updated_at: now, jsonCache: null,
      };
      repo.issues.push(iss);
      sendJson(res, 201, issueJson(repo, iss));
      return true;
    }
    if (rest === '/issues' && method === 'GET') {
      let list = [...repo.issues];
      const state = q.get('state') ?? 'open';
      if (state !== 'all') list = list.filter((i) => i.state === state);
      const dir = q.get('direction') ?? 'desc';
      const sort = q.get('sort') ?? 'created';
      if (sort === 'created') list.sort((a, b) => (dir === 'asc' ? a.seq - b.seq : b.seq - a.seq));
      const { page } = paginate(list, q);
      sendJson(res, 200, page.map((i) => issueJson(repo, i)));
      return true;
    }
    const issueOne = rest.match(/^\/issues\/(\d+)(\/.*)?$/);
    if (issueOne) {
      const num = Number(issueOne[1]);
      const iss = repo.issues.find((i) => i.number === num);
      if (!iss) { sendErr(res, 404, 'Not Found'); return true; }
      const tail = issueOne[2] ?? '';
      if (tail === '' && method === 'GET') {
        if (iss.jsonCache !== null) { sendJsonText(res, 200, iss.jsonCache); return true; }
        const text = `${JSON.stringify(issueJson(repo, iss))}\n`;
        iss.jsonCache = text;
        sendJsonText(res, 200, text);
        return true;
      }
      if (tail === '' && method === 'PATCH') {
        const body = await readJson();
        if (body === null) return true;
        const b = (body ?? {}) as Record<string, unknown>;
        if (b.state === 'closed' || b.state === 'open') iss.state = b.state;
        if (typeof b.title === 'string') iss.title = b.title;
        if (typeof b.body === 'string') iss.body = b.body;
        iss.updated_at = nowIso();
        iss.jsonCache = null;
        sendJson(res, 200, issueJson(repo, iss));
        return true;
      }
      if (tail === '/comments' && method === 'POST') {
        const body = await readJson();
        if (body === null) return true;
        const b = (body ?? {}) as Record<string, unknown>;
        repo.commentSeq += 1;
        const c: Comment = { id: globalIdSeq++, body: typeof b.body === 'string' ? b.body : '', created_at: nowIso() };
        iss.comments.push(c);
        iss.jsonCache = null;
        sendJson(res, 201, { id: c.id, node_id: commentGid(repo, iss, c), body: c.body, user: { login: VIEWER_LOGIN, id: VIEWER_ID }, created_at: c.created_at, updated_at: c.created_at, html_url: '' });
        return true;
      }
      if (tail === '/comments' && method === 'GET') {
        sendJson(res, 200, iss.comments.map((c) => ({ id: c.id, node_id: commentGid(repo, iss, c), body: c.body, user: { login: VIEWER_LOGIN, id: VIEWER_ID }, created_at: c.created_at, updated_at: c.created_at })));
        return true;
      }
    }
    // Pulls
    if (rest === '/pulls' && method === 'POST') {
      const body = await readJson();
      if (body === null) return true;
      const b = (body ?? {}) as Record<string, unknown>;
      const title = typeof b.title === 'string' ? b.title : '';
      let head = typeof b.head === 'string' ? b.head : '';
      let base = typeof b.base === 'string' ? b.base : repo.default_branch;
      if (head.includes(':')) head = head.split(':').pop()!;
      if (base.includes(':')) base = base.split(':').pop()!;
      if (!title || !head) { sendErr(res, 422, 'title and head are required'); return true; }
      const headSha = refTip(repo, head);
      const baseSha = refTip(repo, base);
      if (!headSha || !baseSha) { sendErr(res, 422, 'head or base branch not found'); return true; }
      repo.prSeq += 1;
      const now = nowIso();
      const pr: Pull = {
        id: globalIdSeq++, number: repo.prSeq, title, body: typeof b.body === 'string' ? b.body : '',
        state: 'open', merged: false, headRef: head, baseRef: base,
        headSha, baseSha, mergeSha: null, merged_at: null, seq: repo.prSeq,
        created_at: now, updated_at: now,
      };
      repo.pulls.push(pr);
      sendJson(res, 201, pullJson(repo, pr));
      return true;
    }
    if (rest === '/pulls' && method === 'GET') {
      let list = [...repo.pulls];
      const state = q.get('state') ?? 'open';
      if (state !== 'all') list = list.filter((p) => p.state === state);
      list.sort((a, b) => b.seq - a.seq);
      const { page } = paginate(list, q);
      sendJson(res, 200, page.map((p) => pullJson(repo, p)));
      return true;
    }
    const pullOne = rest.match(/^\/pulls\/(\d+)(\/.*)?$/);
    if (pullOne) {
      const num = Number(pullOne[1]);
      const pr = repo.pulls.find((p) => p.number === num);
      const tail = pullOne[2] ?? '';
      if (tail === '/files' && method === 'GET') {
        if (!pr) { sendErr(res, 404, 'Not Found'); return true; }
        sendJson(res, 200, prFiles(repo, pr));
        return true;
      }
      if (tail === '/merge' && method === 'PUT') {
        if (!pr) { sendErr(res, 404, 'Not Found'); return true; }
        if (pr.state === 'closed') { sendErr(res, 405, 'Pull request already merged or closed'); return true; }
        if (prConflict(repo, pr)) { sendErr(res, 405, 'Merge conflict'); return true; }
        const body = await readJson();
        void body;
        const sha = squashMerge(repo, pr);
        pr.merged = true;
        pr.state = 'closed';
        pr.mergeSha = sha;
        pr.merged_at = nowIso();
        pr.updated_at = pr.merged_at;
        sendJson(res, 200, { sha, merged: true, message: `Pull request #${pr.number} successfully merged` });
        return true;
      }
      if (tail === '' && method === 'GET') {
        if (!pr) { sendErr(res, 404, 'Not Found'); return true; }
        sendJson(res, 200, pullJson(repo, pr));
        return true;
      }
      if (!pr) { sendErr(res, 404, 'Not Found'); return true; }
    }
    sendErr(res, 404, 'Not Found');
    return true;
  }
  sendErr(res, 404, 'Not Found');
  return true;
}

// ---------------------------------------------------------------- GraphQL
// A small parser for the documents gh / github-mcp-server send.
type GqlValue =
  | { kind: 'variable'; name: string }
  | { kind: 'string'; value: string }
  | { kind: 'int'; value: number }
  | { kind: 'bool'; value: boolean }
  | { kind: 'null' }
  | { kind: 'enum'; value: string }
  | { kind: 'list'; values: GqlValue[] }
  | { kind: 'object'; fields: Array<{ name: string; value: GqlValue }> };
interface GqlField {
  alias: string | null; name: string; args: Array<{ name: string; value: GqlValue }>;
  children: GqlField[]; fragment: string | null;
}
interface GqlOp { type: 'query' | 'mutation'; name: string | null; fields: GqlField[]; fragments: Map<string, GqlField[]>; }
class GqlParser {
  private pos = 0;
  private src: string;
  constructor(src: string) { this.src = src; }
  private skipWs(): void {
    for (;;) {
      while (this.pos < this.src.length && /\s/.test(this.src[this.pos]!)) this.pos += 1;
      if (this.src[this.pos] === '#') { while (this.pos < this.src.length && this.src[this.pos] !== '\n') this.pos += 1; continue; }
      if (this.src.startsWith('...', this.pos)) break;
      break;
    }
  }
  private peek(): string { this.skipWs(); return this.src[this.pos] ?? ''; }
  private expect(ch: string): void {
    this.skipWs();
    if (this.src[this.pos] !== ch) throw new Error(`expected ${ch} at ${this.pos}`);
    this.pos += 1;
  }
  private readName(): string {
    this.skipWs();
    const m = /^[A-Za-z_][A-Za-z0-9_]*/.exec(this.src.slice(this.pos));
    if (!m) throw new Error(`expected name at ${this.pos}`);
    this.pos += m[0].length;
    return m[0];
  }
  private readString(): string {
    this.skipWs();
    if (this.src[this.pos] !== '"') throw new Error('expected string');
    this.pos += 1;
    let out = '';
    while (this.pos < this.src.length && this.src[this.pos] !== '"') {
      if (this.src[this.pos] === '\\') {
        const esc = this.src[this.pos + 1];
        if (esc === 'n') out += '\n';
        else if (esc === 't') out += '\t';
        else if (esc === 'r') out += '\r';
        else out += esc ?? '';
        this.pos += 2;
      } else { out += this.src[this.pos]; this.pos += 1; }
    }
    this.pos += 1;
    return out;
  }
  parseValue(): GqlValue {
    this.skipWs();
    const ch = this.src[this.pos];
    if (ch === '$') { this.pos += 1; return { kind: 'variable', name: this.readName() }; }
    if (ch === '"') return { kind: 'string', value: this.readString() };
    if (ch === '[') {
      this.pos += 1;
      const values: GqlValue[] = [];
      while (this.peek() !== ']') {
        if (this.peek() === ',') { this.pos += 1; continue; }
        values.push(this.parseValue());
      }
      this.expect(']');
      return { kind: 'list', values };
    }
    if (ch === '{') {
      this.pos += 1;
      const fields: Array<{ name: string; value: GqlValue }> = [];
      while (this.peek() !== '}') {
        if (this.peek() === ',') { this.pos += 1; continue; }
        const name = this.readName();
        this.expect(':');
        fields.push({ name, value: this.parseValue() });
      }
      this.expect('}');
      return { kind: 'object', fields };
    }
    if (this.src.startsWith('true', this.pos)) { this.pos += 4; return { kind: 'bool', value: true }; }
    if (this.src.startsWith('false', this.pos)) { this.pos += 5; return { kind: 'bool', value: false }; }
    if (this.src.startsWith('null', this.pos)) { this.pos += 4; return { kind: 'null' }; }
    const num = /^-?\d+(\.\d+)?/.exec(this.src.slice(this.pos));
    if (num) { this.pos += num[0].length; return { kind: 'int', value: Number(num[0]) }; }
    return { kind: 'enum', value: this.readName() };
  }
  private parseArgs(): Array<{ name: string; value: GqlValue }> {
    const args: Array<{ name: string; value: GqlValue }> = [];
    this.skipWs();
    if (this.src[this.pos] !== '(') return args;
    this.pos += 1;
    while (this.peek() !== ')') {
      if (this.peek() === ',') { this.pos += 1; continue; }
      const name = this.readName();
      this.expect(':');
      args.push({ name, value: this.parseValue() });
    }
    this.expect(')');
    return args;
  }
  private parseSelectionSet(): GqlField[] {
    this.expect('{');
    const fields: GqlField[] = [];
    while (this.peek() !== '}') {
      if (this.src.startsWith('...', this.pos)) {
        this.pos += 3;
        this.skipWs();
        if (this.src.startsWith('on ', this.pos)) {
          this.pos += 3;
          const typeName = this.readName();
          const children = this.parseSelectionSet();
          fields.push({ alias: null, name: '', args: [], children, fragment: `on:${typeName}` });
        } else {
          const fragName = this.readName();
          fields.push({ alias: null, name: '', args: [], children: [], fragment: fragName });
        }
        continue;
      }
      const first = this.readName();
      let alias: string | null = null;
      let name = first;
      this.skipWs();
      if (this.src[this.pos] === ':') { this.pos += 1; alias = first; name = this.readName(); }
      const args = this.parseArgs();
      let children: GqlField[] = [];
      this.skipWs();
      if (this.src[this.pos] === '{') children = this.parseSelectionSet();
      fields.push({ alias, name, args, children, fragment: null });
    }
    this.expect('}');
    return fields;
  }
  parseDocument(): GqlOp[] {
    const ops: GqlOp[] = [];
    const fragments = new Map<string, GqlField[]>();
    for (;;) {
      this.skipWs();
      if (this.pos >= this.src.length) break;
      if (this.src.startsWith('fragment ', this.pos)) {
        this.pos += 'fragment '.length;
        const name = this.readName();
        this.readName(); // 'on'
        this.readName(); // type
        fragments.set(name, this.parseSelectionSet());
        continue;
      }
      let type: 'query' | 'mutation' = 'query';
      let name: string | null = null;
      if (this.src.startsWith('query', this.pos) || this.src.startsWith('mutation', this.pos)) {
        type = this.src.startsWith('mutation', this.pos) ? 'mutation' : 'query';
        this.pos += type.length;
        this.skipWs();
        if (/[A-Za-z_]/.test(this.src[this.pos] ?? '')) name = this.readName();
        // variable definitions (...)
        this.skipWs();
        if (this.src[this.pos] === '(') {
          let depth = 0;
          while (this.pos < this.src.length) {
            const c = this.src[this.pos]!;
            if (c === '(') depth += 1;
            else if (c === ')') { depth -= 1; this.pos += 1; if (depth === 0) break; continue; }
            this.pos += 1;
          }
        }
      }
      const fields = this.parseSelectionSet();
      ops.push({ type, name, fields, fragments });
    }
    return ops;
  }
}
function gqlArgValue(v: GqlValue, vars: Record<string, unknown>): unknown {
  switch (v.kind) {
    case 'variable': return vars[v.name];
    case 'string': return v.value;
    case 'int': return v.value;
    case 'bool': return v.value;
    case 'null': return null;
    case 'enum': return v.value;
    case 'list': return v.values.map((x) => gqlArgValue(x, vars));
    case 'object': {
      const o: Record<string, unknown> = {};
      for (const f of v.fields) o[f.name] = gqlArgValue(f.value, vars);
      return o;
    }
  }
}
function gqlArgs(f: GqlField, vars: Record<string, unknown>): Record<string, unknown> {
  const o: Record<string, unknown> = {};
  for (const a of f.args) o[a.name] = gqlArgValue(a.value, vars);
  return o;
}
const ISSUE_TYPE_FIELDS = ['id', 'number', 'title', 'state', 'body', 'createdAt', 'updatedAt', 'url', 'author', 'labels', 'comments'];
const PR_TYPE_FIELDS = ['id', 'number', 'headRefName', 'baseRefName', 'mergeable', 'state', 'merged', 'files', 'title', 'body', 'createdAt', 'updatedAt', 'url', 'author'];
const REPO_TYPE_FIELDS = ['id', 'databaseId', 'name', 'nameWithOwner', 'owner', 'defaultBranchRef', 'viewerPermission', 'hasIssuesEnabled', 'issue', 'issues', 'pullRequests', 'pullRequest', 'createdAt', 'updatedAt', 'description', 'isPrivate', 'url'];
const SEARCH_ENUM = ['ISSUE', 'REPOSITORY', 'USER', 'DISCUSSION'];
interface GqlCtx { login: string; vars: Record<string, unknown>; errors: Array<{ message: string }>; }
function decodeGid(kind: string, id: string): string | null {
  if (!id.startsWith(`${kind}_`)) return null;
  try {
    const hex = Buffer.from(id.slice(kind.length + 1), 'base64url').toString('utf8');
    return hex.length === 24 ? hex : null;
  } catch { return null; }
}
function findRepoByGid(id: string): Repo | null {
  const hex = decodeGid('R', id);
  if (!hex) return null;
  for (const r of repos.values()) {
    if (sha1hex(`R:${repoKey(r.owner, r.name)}`).slice(0, 24) === hex) return r;
  }
  return null;
}
function findIssueByGid(id: string): { repo: Repo; issue: Issue } | null {
  const hex = decodeGid('I', id);
  if (!hex) return null;
  for (const r of repos.values()) {
    for (const iss of r.issues) {
      if (sha1hex(`I:${repoKey(r.owner, r.name)}#${iss.number}`).slice(0, 24) === hex) return { repo: r, issue: iss };
    }
  }
  return null;
}
function findPullByGid(id: string): { repo: Repo; pull: Pull } | null {
  const hex = decodeGid('PR', id);
  if (!hex) return null;
  for (const r of repos.values()) {
    for (const pr of r.pulls) {
      if (sha1hex(`PR:${repoKey(r.owner, r.name)}#${pr.number}`).slice(0, 24) === hex) return { repo: r, pull: pr };
    }
  }
  return null;
}
function cursorOf(n: number): string {
  return b64url(`cursor:${n}`);
}
function cursorNum(c: string | null | undefined): number | null {
  if (!c) return null;
  try {
    const s = Buffer.from(c, 'base64url').toString('utf8');
    const m = /^cursor:(\d+)$/.exec(s);
    return m ? Number(m[1]) : null;
  } catch { return null; }
}
function execFields(fields: GqlField[], parent: unknown, kind: string, ctx: GqlCtx, op: GqlOp): Record<string, unknown> {
  const out: Record<string, unknown> = {};
  for (const f of fields) {
    if (f.fragment) {
      if (f.fragment.startsWith('on:')) {
        const typeName = f.fragment.slice(3);
        const matches = (kind === 'node' && typeName === 'Repository' && parent !== null && typeof parent === 'object' && (parent as Record<string, unknown>).__kind === 'repo')
          || (kind === 'repo' && typeName === 'Repository');
        if (matches) Object.assign(out, execFields(f.children, parent, kind, ctx, op));
        continue;
      }
      const frag = op.fragments.get(f.fragment);
      if (frag) Object.assign(out, execFields(frag, parent, kind, ctx, op));
      continue;
    }
    const key = f.alias ?? f.name;
    out[key] = execField(f, parent, kind, ctx, op);
  }
  return out;
}
function unknownField(ctx: GqlCtx, name: string): null {
  ctx.errors.push({ message: `Cannot query field "${name}" on type "Viewer". Did you mean to use an inline fragment on "${name}"? Field "${name}" does not exist.` });
  return null;
}
function execField(f: GqlField, parent: unknown, kind: string, ctx: GqlCtx, op: GqlOp): unknown {
  const args = gqlArgs(f, ctx.vars);
  if (kind.endsWith('Payload')) return execPayloadField(f, parent, ctx, op);
  if (kind === 'pageInfo') {
    const p = parent as Record<string, unknown>;
    if (f.name === 'hasNextPage') return p.hasNextPage ?? false;
    if (f.name === 'endCursor') return p.endCursor ?? null;
    if (f.name === 'hasPreviousPage') return false;
    if (f.name === 'startCursor') return null;
    return null;
  }
  if (kind === 'root') {
    if (f.name === 'viewer') {
      return execFields(f.children, { login: ctx.login }, 'viewer', ctx, op);
    }
    if (f.name === 'repository') {
      const owner = String(args.owner ?? '');
      const name = String(args.name ?? '');
      const repo = owner === ctx.login ? repos.get(repoKey(owner, name)) ?? null : null;
      if (!repo) return null;
      return execFields(f.children, repo, 'repo', ctx, op);
    }
    if (f.name === 'node') {
      const id = String(args.id ?? '');
      const repo = findRepoByGid(id);
      if (!repo) return null;
      const nodeObj: Record<string, unknown> = { __kind: 'repo', __repo: repo };
      const base = execFields(f.children.filter((c) => !c.fragment), nodeObj, 'node', ctx, op);
      const frag = execFields(f.children.filter((c) => !!c.fragment), nodeObj, 'node', ctx, op);
      return { ...base, ...frag };
    }
    if (f.name === '__type') {
      const tname = String(args.name ?? '');
      const typeMap: Record<string, { fields: string[]; enums: string[] }> = {
        Issue: { fields: ISSUE_TYPE_FIELDS, enums: [] },
        PullRequest: { fields: PR_TYPE_FIELDS, enums: [] },
        Repository: { fields: REPO_TYPE_FIELDS, enums: [] },
        SearchType: { fields: [], enums: SEARCH_ENUM },
      };
      const t = typeMap[tname];
      if (!t) return null;
      const out: Record<string, unknown> = { name: tname };
      for (const child of f.children) {
        if (child.name === 'fields') out[child.alias ?? 'fields'] = t.fields.map((n) => ({ name: n }));
        else if (child.name === 'enumValues') out[child.alias ?? 'enumValues'] = t.enums.map((n) => ({ name: n }));
        else if (child.name === 'name') out.name = tname;
      }
      return out;
    }
    if (f.name === 'createIssue' || f.name === 'closeIssue' || f.name === 'createPullRequest' || f.name === 'mergePullRequest' || f.name === 'addComment') {
      return execMutation(f, ctx, op);
    }
    ctx.errors.push({ message: `Cannot query field "${f.name}" on type "Query".` });
    return null;
  }
  if (kind === 'viewer') {
    if (f.name === 'login') return ctx.login;
    if (f.name === 'id') return gid('U', ctx.login);
    return unknownField(ctx, f.name);
  }
  if (kind === 'repo') {
    const repo = parent as Repo;
    switch (f.name) {
      case 'id': return repoGid(repo);
      case 'databaseId': return repo.id;
      case 'name': return repo.name;
      case 'nameWithOwner': return repoKey(repo.owner, repo.name);
      case 'owner': return execFields(f.children, { login: repo.owner }, 'owner', ctx, op);
      case 'defaultBranchRef': {
        if (f.children.length === 0) return { name: repo.default_branch };
        return execFields(f.children, { name: repo.default_branch }, 'branchRef', ctx, op);
      }
      case 'viewerPermission': return 'ADMIN';
      case 'hasIssuesEnabled': return true;
      case 'description': return repo.description;
      case 'isPrivate': return repo.private;
      case 'url': return `https://example.invalid/${repo.owner}/${repo.name}`;
      case 'createdAt': return repo.created_at;
      case 'updatedAt': return repo.updated_at;
      case 'issue': {
        const iss = repo.issues.find((i) => i.number === Number(args.number));
        if (!iss) return null;
        return execFields(f.children, { repo, issue: iss }, 'issue', ctx, op);
      }
      case 'issues': return issuesConnection(repo, args, f, ctx, op);
      case 'pullRequests': return pullsConnection(repo, args, f, ctx, op);
      case 'pullRequest': {
        const pr = repo.pulls.find((p) => p.number === Number(args.number));
        if (!pr) return null;
        return execFields(f.children, { repo, pull: pr }, 'pull', ctx, op);
      }
      default:
        ctx.errors.push({ message: `Cannot query field "${f.name}" on type "Repository".` });
        return null;
    }
  }
  if (kind === 'owner') {
    if (f.name === 'login') return (parent as { login: string }).login;
    if (f.name === 'id') return gid('U', (parent as { login: string }).login);
    ctx.errors.push({ message: `Cannot query field "${f.name}" on type "User".` });
    return null;
  }
  if (kind === 'branchRef') {
    if (f.name === 'name') return (parent as { name: string }).name;
    ctx.errors.push({ message: `Cannot query field "${f.name}" on type "Ref".` });
    return null;
  }
  if (kind === 'issue') {
    const { repo, issue } = parent as { repo: Repo; issue: Issue };
    switch (f.name) {
      case 'id': return issueGid(repo, issue);
      case 'number': return issue.number;
      case 'title': return issue.title;
      case 'state': return issue.state.toUpperCase();
      case 'body': return issue.body;
      case 'createdAt': return issue.created_at;
      case 'updatedAt': return issue.updated_at;
      case 'url': return `https://example.invalid/${repo.owner}/${repo.name}/issues/${issue.number}`;
      case 'author': return execFields(f.children, { login: VIEWER_LOGIN }, 'owner', ctx, op);
      case 'labels': {
        const nodes = issue.labels.map((l) => ({ name: l.name }));
        if (f.children.some((c) => c.name === 'nodes')) {
          const out: Record<string, unknown> = {};
          for (const c of f.children) if (c.name === 'nodes') out.nodes = nodes.map((n) => execFields(c.children, n, 'label', ctx, op));
          return out;
        }
        return { nodes };
      }
      case 'comments': {
        const nodes = issue.comments.map((c) => ({ id: commentGid(repo, issue, c), body: c.body }));
        if (f.children.some((c) => c.name === 'nodes')) {
          const out: Record<string, unknown> = {};
          for (const c of f.children) if (c.name === 'nodes') out.nodes = nodes.map((n) => execFields(c.children, n, 'comment', ctx, op));
          return out;
        }
        return { nodes };
      }
      default:
        ctx.errors.push({ message: `Cannot query field "${f.name}" on type "Issue".` });
        return null;
    }
  }
  if (kind === 'label') {
    if (f.name === 'name') return (parent as { name: string }).name;
    return null;
  }
  if (kind === 'comment') {
    if (f.name === 'id') return (parent as { id: string }).id;
    if (f.name === 'body') return (parent as { body: string }).body;
    return null;
  }
  if (kind === 'pull') {
    const { repo, pull } = parent as { repo: Repo; pull: Pull };
    switch (f.name) {
      case 'id': return pullGid(repo, pull);
      case 'number': return pull.number;
      case 'title': return pull.title;
      case 'body': return pull.body;
      case 'headRefName': return pull.headRef;
      case 'baseRefName': return pull.baseRef;
      case 'mergeable': return pull.merged ? 'MERGEABLE' : (isMergeable(repo, pull) ? 'MERGEABLE' : 'CONFLICTING');
      case 'state': return pull.merged ? 'MERGED' : pull.state.toUpperCase();
      case 'merged': return pull.merged;
      case 'createdAt': return pull.created_at;
      case 'updatedAt': return pull.updated_at;
      case 'url': return `https://example.invalid/${repo.owner}/${repo.name}/pull/${pull.number}`;
      case 'author': return execFields(f.children, { login: VIEWER_LOGIN }, 'owner', ctx, op);
      case 'files': {
        const files = prFiles(repo, pull).map((x) => ({ path: x.filename }));
        const first = typeof args.first === 'number' ? args.first : 10;
        const nodes = files.slice(0, first);
        if (f.children.some((c) => c.name === 'nodes')) {
          const out: Record<string, unknown> = {};
          for (const c of f.children) if (c.name === 'nodes') out.nodes = nodes.map((n) => execFields(c.children, n, 'file', ctx, op));
          return out;
        }
        return { nodes };
      }
      default:
        ctx.errors.push({ message: `Cannot query field "${f.name}" on type "PullRequest".` });
        return null;
    }
  }
  if (kind === 'node') {
    const repo = (parent as Record<string, unknown>).__repo as Repo;
    if (f.name === 'id') return repoGid(repo);
    if (f.name === 'name') return repo.name;
    if (f.name === 'nameWithOwner') return repoKey(repo.owner, repo.name);
    ctx.errors.push({ message: `Cannot query field "${f.name}" on type "Node".` });
    return null;
  }
  if (kind === 'file') {
    if (f.name === 'path') return (parent as { path: string }).path;
    return null;
  }
  ctx.errors.push({ message: `Cannot query field "${f.name}".` });
  return null;
}
function issuesConnection(repo: Repo, args: Record<string, unknown>, f: GqlField, ctx: GqlCtx, op: GqlOp): Record<string, unknown> {
  let list = [...repo.issues];
  const states = args.states as string[] | undefined;
  if (states && states.length > 0) {
    const want = new Set(states.map((s) => String(s).toUpperCase()));
    list = list.filter((i) => want.has(i.state.toUpperCase()));
  }
  const orderBy = args.orderBy as Record<string, unknown> | undefined;
  if (orderBy && String(orderBy.field ?? '') === 'CREATED_AT') {
    list.sort((a, b) => (String(orderBy.direction ?? 'ASC') === 'DESC' ? b.number - a.number : a.number - b.number));
  } else {
    list.sort((a, b) => a.number - b.number);
  }
  const after = cursorNum(args.after as string | null | undefined);
  if (after !== null) {
    const dirDesc = orderBy && String(orderBy.direction ?? '') === 'DESC';
    list = dirDesc ? list.filter((i) => i.number < after) : list.filter((i) => i.number > after);
  }
  const first = typeof args.first === 'number' ? args.first : list.length;
  const page = list.slice(0, first);
  const nodesField = f.children.find((c) => c.name === 'nodes');
  const pageInfoField = f.children.find((c) => c.name === 'pageInfo');
  const out: Record<string, unknown> = {};
  if (nodesField) out.nodes = page.map((iss) => execFields(nodesField.children, { repo, issue: iss }, 'issue', ctx, op));
  if (pageInfoField) {
    const hasNext = list.length > page.length;
    const endCursor = page.length > 0 ? cursorOf(page[page.length - 1]!.number) : null;
    out.pageInfo = execFields(pageInfoField.children, { hasNextPage: hasNext, endCursor }, 'pageInfo', ctx, op);
  }
  if (!nodesField && !pageInfoField) {
    out.nodes = page.map((iss) => execFields(f.children, { repo, issue: iss }, 'issue', ctx, op));
  }
  return out;
}
function pullsConnection(repo: Repo, args: Record<string, unknown>, f: GqlField, ctx: GqlCtx, op: GqlOp): Record<string, unknown> {
  let list = [...repo.pulls];
  const states = args.states as string[] | undefined;
  if (states && states.length > 0) {
    const want = new Set(states.map((s) => String(s).toUpperCase()));
    list = list.filter((p) => want.has(p.merged ? 'MERGED' : p.state.toUpperCase()));
  }
  list.sort((a, b) => b.number - a.number);
  const first = typeof args.first === 'number' ? args.first : list.length;
  const page = list.slice(0, first);
  const nodesField = f.children.find((c) => c.name === 'nodes');
  const out: Record<string, unknown> = {};
  if (nodesField) out.nodes = page.map((pr) => execFields(nodesField.children, { repo, pull: pr }, 'pull', ctx, op));
  else out.nodes = page.map((pr) => execFields(f.children, { repo, pull: pr }, 'pull', ctx, op));
  return out;
}
function execMutation(f: GqlField, ctx: GqlCtx, op: GqlOp): unknown {
  const args = gqlArgs(f, ctx.vars);
  const input = (args.input ?? {}) as Record<string, unknown>;
  if (f.name === 'createIssue') {
    const repo = findRepoByGid(String(input.repositoryId ?? ''));
    if (!repo) { ctx.errors.push({ message: 'Repository not found' }); return null; }
    repo.issueSeq += 1;
    const now = nowIso();
    const iss: Issue = {
      id: globalIdSeq++, number: repo.issueSeq, title: String(input.title ?? ''),
      body: typeof input.body === 'string' ? input.body : '', state: 'open', labels: [],
      comments: [], seq: repo.issueSeq, created_at: now, updated_at: now, jsonCache: null,
    };
    repo.issues.push(iss);
    return execFields(f.children, { issue: iss, repo }, 'createIssuePayload', ctx, op);
  }
  if (f.name === 'closeIssue') {
    const found = findIssueByGid(String(input.issueId ?? ''));
    if (!found) { ctx.errors.push({ message: 'Issue not found' }); return null; }
    found.issue.state = 'closed';
    found.issue.updated_at = nowIso();
    found.issue.jsonCache = null;
    return execFields(f.children, { issue: found.issue, repo: found.repo }, 'closeIssuePayload', ctx, op);
  }
  if (f.name === 'createPullRequest') {
    const repo = findRepoByGid(String(input.repositoryId ?? ''));
    if (!repo) { ctx.errors.push({ message: 'Repository not found' }); return null; }
    const head = String(input.headRefName ?? '');
    const base = String(input.baseRefName ?? 'main');
    const headSha = refTip(repo, head);
    const baseSha = refTip(repo, base);
    if (!headSha || !baseSha) { ctx.errors.push({ message: 'head or base branch not found' }); return null; }
    repo.prSeq += 1;
    const now = nowIso();
    const pr: Pull = {
      id: globalIdSeq++, number: repo.prSeq, title: String(input.title ?? ''),
      body: typeof input.body === 'string' ? input.body : '', state: 'open', merged: false,
      headRef: head, baseRef: base, headSha, baseSha, mergeSha: null, merged_at: null,
      seq: repo.prSeq, created_at: now, updated_at: now,
    };
    repo.pulls.push(pr);
    return execFields(f.children, { pull: pr, repo }, 'createPullPayload', ctx, op);
  }
  if (f.name === 'mergePullRequest') {
    const found = findPullByGid(String(input.pullRequestId ?? ''));
    if (!found) { ctx.errors.push({ message: 'Pull request not found' }); return null; }
    const { repo, pull } = found;
    if (!pull.merged && pull.state === 'open' && !prConflict(repo, pull)) {
      const sha = squashMerge(repo, pull);
      pull.merged = true;
      pull.state = 'closed';
      pull.mergeSha = sha;
      pull.merged_at = nowIso();
      pull.updated_at = pull.merged_at;
    }
    return execFields(f.children, { pull, repo }, 'mergePullPayload', ctx, op);
  }
  if (f.name === 'addComment') {
    const found = findIssueByGid(String(input.subjectId ?? ''));
    if (!found) { ctx.errors.push({ message: 'Issue not found' }); return null; }
    const { repo, issue } = found;
    repo.commentSeq += 1;
    const c: Comment = { id: globalIdSeq++, body: String(input.body ?? ''), created_at: nowIso() };
    issue.comments.push(c);
    issue.jsonCache = null;
    const out: Record<string, unknown> = {};
    for (const child of f.children) {
      if (child.name === 'commentEdge') {
        const nodeField = child.children.find((x) => x.name === 'node');
        out.commentEdge = nodeField ? { node: execFields(nodeField.children, { id: commentGid(repo, issue, c), body: c.body }, 'comment', ctx, op) } : { node: { id: commentGid(repo, issue, c), body: c.body } };
      } else if (child.name === 'clientMutationId') out.clientMutationId = null;
    }
    return out;
  }
  return null;
}
function execPayloadField(f: GqlField, parent: unknown, ctx: GqlCtx, op: GqlOp): unknown {
  const p = parent as Record<string, unknown>;
  if (f.name === 'issue' && p.issue) return execFields(f.children, { repo: p.repo, issue: p.issue as Issue }, 'issue', ctx, op);
  if (f.name === 'pullRequest' && p.pull) return execFields(f.children, { repo: p.repo, pull: p.pull as Pull }, 'pull', ctx, op);
  if (f.name === 'commentEdge') return p.commentEdge ?? null;
  return null;
}
// (Payload kinds are routed at the top of execField.)

// ---------------------------------------------------------------- GraphQL HTTP
function runGraphQLOp(query: string, vars: Record<string, unknown>, login: string): { data: Record<string, unknown> | null; errors?: Array<{ message: string }> } {
  const ctx: GqlCtx = { login, vars, errors: [] };
  let ops: GqlOp[];
  try {
    ops = new GqlParser(query).parseDocument();
  } catch (e) {
    return { data: null, errors: [{ message: e instanceof Error ? e.message : 'parse error' }] };
  }
  if (ops.length === 0) return { data: {}, errors: [{ message: 'empty query' }] };
  const op = ops[0]!;
  const data = execFields(op.fields, null, 'root', ctx, op);
  if (ctx.errors.length > 0) return { data, errors: ctx.errors };
  return { data };
}
async function handleGraphQL(req: IncomingMessage, res: ServerResponse): Promise<boolean> {
  if (pathOf(req) !== '/api/graphql') return false;
  const login = requireAuth(req, res);
  if (login === null) return true;
  const buf = await readBody(req);
  const parsed = parseJsonBody(buf);
  if (!parsed.ok) { sendErr(res, 400, 'Problems parsing JSON'); return true; }
  const body = parsed.value;
  if (Array.isArray(body)) {
    const out = body.map((item) => {
      const q = (item as Record<string, unknown>).query;
      const v = (item as Record<string, unknown>).variables;
      if (typeof q !== 'string') return { data: null, errors: [{ message: 'query must be a string' }] };
      return runGraphQLOp(q, (v ?? {}) as Record<string, unknown>, login);
    });
    sendJson(res, 200, out);
    return true;
  }
  const q = (body as Record<string, unknown>).query;
  const v = (body as Record<string, unknown>).variables;
  if (typeof q !== 'string') { sendJson(res, 200, { data: null, errors: [{ message: 'query must be a string' }] }); return true; }
  sendJson(res, 200, runGraphQLOp(q, (v ?? {}) as Record<string, unknown>, login));
  return true;
}

// ---------------------------------------------------------------- MCP
interface McpTool {
  name: string; description: string;
  inputSchema: { type: 'object'; properties: Record<string, Record<string, unknown>>; required: string[] };
}
const MCP_TOOLS: McpTool[] = [
  {
    name: 'create_repo', description: 'Create a repository owned by the authenticated user.',
    inputSchema: { type: 'object', properties: { name: { type: 'string', description: 'Repository name' }, owner: { type: 'string', description: 'Owner login' }, description: { type: 'string', description: 'Repository description' }, private: { type: 'boolean', description: 'Whether the repository is private' } }, required: ['name'] },
  },
  {
    name: 'get_repo', description: 'Get a repository by owner and name.',
    inputSchema: { type: 'object', properties: { owner: { type: 'string', description: 'Owner login' }, repo: { type: 'string', description: 'Repository name' } }, required: ['owner', 'repo'] },
  },
  {
    name: 'create_issue', description: 'Create an issue in a repository.',
    inputSchema: { type: 'object', properties: { owner: { type: 'string', description: 'Owner login' }, repo: { type: 'string', description: 'Repository name' }, title: { type: 'string', description: 'Issue title' }, body: { type: 'string', description: 'Issue body' } }, required: ['owner', 'repo', 'title'] },
  },
  {
    name: 'list_issues', description: 'List issues in a repository.',
    inputSchema: { type: 'object', properties: { owner: { type: 'string', description: 'Owner login' }, repo: { type: 'string', description: 'Repository name' }, state: { type: 'string', description: 'Issue state: open, closed, or all' } }, required: ['owner', 'repo'] },
  },
  {
    name: 'create_pull_request', description: 'Create a pull request in a repository.',
    inputSchema: { type: 'object', properties: { owner: { type: 'string', description: 'Owner login' }, repo: { type: 'string', description: 'Repository name' }, title: { type: 'string', description: 'Pull request title' }, body: { type: 'string', description: 'Pull request body' }, head: { type: 'string', description: 'Head branch name' }, base: { type: 'string', description: 'Base branch name' } }, required: ['owner', 'repo', 'title', 'head', 'base'] },
  },
  {
    name: 'merge_pull_request', description: 'Merge a pull request in a repository.',
    inputSchema: { type: 'object', properties: { owner: { type: 'string', description: 'Owner login' }, repo: { type: 'string', description: 'Repository name' }, pull_number: { type: 'integer', description: 'Pull request number' } }, required: ['owner', 'repo', 'pull_number'] },
  },
];
function normToolName(s: string): string {
  return s.toLowerCase().replace(/[^a-z0-9]/g, '');
}
const TOOL_ALIASES: Record<string, string> = {
  createrepository: 'create_repo', repocreate: 'create_repo', reposcreate: 'create_repo', repositorycreate: 'create_repo',
  getrepository: 'get_repo', repoget: 'get_repo', reposget: 'get_repo', repositoryget: 'get_repo',
  issuecreate: 'create_issue', issuescreate: 'create_issue',
  issueslist: 'list_issues', issuelist: 'list_issues',
  pullrequestcreate: 'create_pull_request', pullscreate: 'create_pull_request', createpr: 'create_pull_request', prcreate: 'create_pull_request',
  pullrequestmerge: 'merge_pull_request', pullsmerge: 'merge_pull_request', mergepr: 'merge_pull_request', prmerge: 'merge_pull_request',
};
function resolveTool(name: string): McpTool | null {
  const n = normToolName(name);
  for (const t of MCP_TOOLS) {
    if (normToolName(t.name) === n) return t;
    if (n.endsWith(normToolName(t.name))) return t;
  }
  const alias = TOOL_ALIASES[n];
  if (alias) return MCP_TOOLS.find((t) => t.name === alias) ?? null;
  return null;
}
function mcpTextResult(obj: unknown): Record<string, unknown> {
  return { content: [{ type: 'text', text: JSON.stringify(obj) }], structuredContent: obj };
}
function mcpErrorResult(message: string): Record<string, unknown> {
  return { content: [{ type: 'text', text: message }], isError: true };
}
function callTool(name: string, args: Record<string, unknown>, login: string): Record<string, unknown> {
  const tool = resolveTool(name);
  if (!tool) return { __rpcError: -32601, __message: `Unknown tool: ${name}` };
  const required = tool.inputSchema.required;
  for (const r of required) {
    if (args[r] === undefined || args[r] === null || args[r] === '') return mcpErrorResult(`Missing required argument: ${r}`);
  }
  const owner = typeof args.owner === 'string' && args.owner ? args.owner : login;
  const repoName = typeof args.repo === 'string' ? args.repo : (typeof args.name === 'string' ? args.name : '');
  if (tool.name === 'create_repo') {
    const rname = String(args.name ?? '');
    if (!rname) return mcpErrorResult('Missing required argument: name');
    if (repos.has(repoKey(owner, rname))) return mcpErrorResult(`Repository ${owner}/${rname} already exists`);
    const repo = newRepo(owner, rname, args.private === true, typeof args.description === 'string' ? args.description : '');
    const out = { ...repoJson(repo), full_name: repoKey(owner, rname) };
    return mcpTextResult(out);
  }
  const repo = owner === login ? repos.get(repoKey(owner, repoName)) ?? null : null;
  if (!repo) return mcpErrorResult(`Repository not found: ${owner}/${repoName}`);
  if (tool.name === 'get_repo') return mcpTextResult({ ...repoJson(repo), full_name: repoKey(repo.owner, repo.name) });
  if (tool.name === 'create_issue') {
    const title = String(args.title ?? '');
    repo.issueSeq += 1;
    const now = nowIso();
    const iss: Issue = {
      id: globalIdSeq++, number: repo.issueSeq, title,
      body: typeof args.body === 'string' ? args.body : '', state: 'open', labels: [],
      comments: [], seq: repo.issueSeq, created_at: now, updated_at: now, jsonCache: null,
    };
    repo.issues.push(iss);
    return mcpTextResult(issueJson(repo, iss));
  }
  if (tool.name === 'list_issues') {
    const state = typeof args.state === 'string' ? args.state : 'open';
    let list = [...repo.issues];
    if (state !== 'all') list = list.filter((i) => i.state === state);
    list.sort((a, b) => a.seq - b.seq);
    return mcpTextResult({ issues: list.map((i) => issueJson(repo, i)), total_count: list.length });
  }
  if (tool.name === 'create_pull_request') {
    let head = String(args.head ?? '');
    let base = String(args.base ?? 'main');
    if (head.includes(':')) head = head.split(':').pop()!;
    if (base.includes(':')) base = base.split(':').pop()!;
    const headSha = refTip(repo, head);
    const baseSha = refTip(repo, base);
    if (!headSha || !baseSha) return mcpErrorResult('head or base branch not found');
    repo.prSeq += 1;
    const now = nowIso();
    const pr: Pull = {
      id: globalIdSeq++, number: repo.prSeq, title: String(args.title ?? ''),
      body: typeof args.body === 'string' ? args.body : '', state: 'open', merged: false,
      headRef: head, baseRef: base, headSha, baseSha, mergeSha: null, merged_at: null,
      seq: repo.prSeq, created_at: now, updated_at: now,
    };
    repo.pulls.push(pr);
    return mcpTextResult(pullJson(repo, pr));
  }
  if (tool.name === 'merge_pull_request') {
    const num = Number(args.pull_number);
    const pr = repo.pulls.find((p) => p.number === num);
    if (!pr) return mcpErrorResult(`Pull request #${num} not found`);
    if (pr.state === 'closed') return mcpErrorResult('Pull request already closed');
    if (prConflict(repo, pr)) return mcpErrorResult('Merge conflict');
    const sha = squashMerge(repo, pr);
    pr.merged = true;
    pr.state = 'closed';
    pr.mergeSha = sha;
    pr.merged_at = nowIso();
    pr.updated_at = pr.merged_at;
    return mcpTextResult({ sha, merged: true, number: pr.number, message: `Pull request #${pr.number} successfully merged` });
  }
  return mcpErrorResult(`Unknown tool: ${name}`);
}
async function handleMcp(req: IncomingMessage, res: ServerResponse): Promise<boolean> {
  if (pathOf(req) !== '/mcp') return false;
  const raw = await readBody(req);
  // Parse errors are answered before any JSON parsing, with the id if one
  // can be recovered from the raw text.
  let body: unknown;
  try {
    body = JSON.parse(raw.toString('utf8'));
  } catch {
    let id: unknown = null;
    const m = /"id"\s*:\s*(\d+|"[^"]*")/.exec(raw.toString('utf8'));
    if (m) { try { id = JSON.parse(m[1]!); } catch { id = null; } }
    res.writeHead(400, { 'content-type': JSON_TYPE, 'x-github-request-id': `req-${(++reqCounter).toString(36)}-${Date.now().toString(36)}` });
    res.end(`${JSON.stringify({ jsonrpc: '2.0', id, error: { code: -32700, message: 'Parse error' } })}\n`);
    return true;
  }
  const login = requireAuth(req, res);
  if (login === null) return true;
  const msg = body as Record<string, unknown>;
  const id = msg.id ?? null;
  const method = typeof msg.method === 'string' ? msg.method : '';
  const params = (msg.params ?? {}) as Record<string, unknown>;
  const reply = (payload: Record<string, unknown>): void => {
    sendJson(res, 200, payload);
  };
  if (method === 'notifications/initialized' || method.startsWith('notifications/')) {
    res.writeHead(202, { 'x-github-request-id': `req-${(++reqCounter).toString(36)}-${Date.now().toString(36)}` });
    res.end();
    return true;
  }
  if (method === 'server/discover') {
    const serverInfo = { name: 'github-core-forge', version: '1.0.0' };
    reply({
      jsonrpc: '2.0', id,
      result: {
        supportedVersions: ['2026-07-28', '2025-11-25', '2025-06-18', '2025-03-26', '2024-11-05'],
        serverInfo, capabilities: { tools: {} },
        _meta: { 'io.modelcontextprotocol/serverInfo': serverInfo, 'io.modelcontextprotocol/protocolVersion': '2026-07-28' },
      },
    });
    return true;
  }
  if (method === 'initialize') {
    const offered = typeof params.protocolVersion === 'string' ? params.protocolVersion : '2025-11-25';
    const chosen = ['2026-07-28', '2025-11-25', '2025-06-18', '2025-03-26', '2024-11-05'].includes(offered) ? offered : '2025-11-25';
    reply({
      jsonrpc: '2.0', id,
      result: {
        protocolVersion: chosen,
        capabilities: { tools: {} },
        serverInfo: { name: 'github-core-forge', version: '1.0.0' },
      },
    });
    return true;
  }
  if (method === 'ping') { reply({ jsonrpc: '2.0', id, result: {} }); return true; }
  if (method === 'tools/list') {
    reply({ jsonrpc: '2.0', id, result: { tools: MCP_TOOLS } });
    return true;
  }
  if (method === 'tools/call') {
    const name = typeof params.name === 'string' ? params.name : '';
    const args = (params.arguments ?? {}) as Record<string, unknown>;
    const out = callTool(name, args, login);
    if (typeof out.__rpcError === 'number') {
      reply({ jsonrpc: '2.0', id, error: { code: out.__rpcError, message: String(out.__message ?? 'Tool error') } });
      return true;
    }
    reply({ jsonrpc: '2.0', id, result: out });
    return true;
  }
  reply({ jsonrpc: '2.0', id, error: { code: -32601, message: `Method not found: ${method}` } });
  return true;
}

// ---------------------------------------------------------------- git smart HTTP
const UPLOAD_CAPS_V0 = 'symref=HEAD:refs/heads/main side-band-64k thin-pack ofs-delta shallow agent=github-core-forge/1.0';
const RECEIVE_CAPS = 'report-status side-band-64k delete-refs ofs-delta symref=HEAD:refs/heads/main agent=github-core-forge/1.0';
function sortedRefs(repo: Repo): Array<{ ref: string; oid: string }> {
  return [...repo.refs.entries()].map(([ref, oid]) => ({ ref, oid })).sort((a, b) => (a.ref < b.ref ? -1 : 1));
}
function isTagObject(oid: string): boolean {
  const o = objects.get(oid);
  return !!o && o.type === 'tag';
}
function tagTarget(oid: string): string | null {
  const o = objects.get(oid);
  if (!o || o.type !== 'tag') return null;
  const m = o.data.toString('utf8').match(/^object ([0-9a-f]{40})$/m);
  return m ? m[1]! : null;
}
function sendAdvertisement(res: ServerResponse, service: string, lines: Buffer[], contentType: string): void {
  const head = pkt(`# service=${service}\n`);
  const body = Buffer.concat([head, pktFlush(), ...lines, pktFlush()]);
  res.writeHead(200, {
    'content-type': contentType,
    'content-length': body.length,
    'x-github-request-id': `req-${(++reqCounter).toString(36)}-${Date.now().toString(36)}`,
  });
  res.end(body);
}
function refLinesV0(repo: Repo, caps: string): Buffer[] {
  const refs = sortedRefs(repo);
  const main = repo.refs.get('refs/heads/main');
  const lines: Buffer[] = [];
  if (refs.length === 0) {
    lines.push(pkt(`${ZERO_OID} capabilities^{}\0${caps}\n`));
    return lines;
  }
  const headOid = main ?? refs[0]!.oid;
  lines.push(pkt(`${headOid} HEAD\0${caps}\n`));
  for (const r of refs) {
    lines.push(pkt(`${r.oid} ${r.ref}\n`));
    if (isTagObject(r.oid)) {
      const target = tagTarget(r.oid);
      if (target) lines.push(pkt(`${target} ${r.ref}^{}\n`));
    }
  }
  return lines;
}
async function handleGit(req: IncomingMessage, res: ServerResponse): Promise<boolean> {
  const path = pathOf(req);
  const method = req.method ?? 'GET';
  const m = path.match(/^\/([^/]+)\/([^/]+)\.git\/(info\/refs|git-upload-pack|git-receive-pack)$/);
  if (!m) return false;
  const owner = decodeURIComponent(m[1]!);
  const name = decodeURIComponent(m[2]!);
  const action = m[3]!;
  const repo = repos.get(repoKey(owner, name)) ?? null;

  if (method === 'GET' && action === 'info/refs') {
    if (!repo) { sendErr(res, 404, 'Not Found'); return true; }
    const service = queryOf(req).get('service') ?? '';
    const v2 = req.headers['git-protocol'] === 'version=2';
    if (service === 'git-upload-pack') {
      if (v2) {
        const body = Buffer.concat([
          pkt('version 2\n'),
          pkt('agent=github-core-forge/1.0\n'),
          pkt('ls-refs=unborn\n'),
          pkt('fetch=shallow filter\n'),
          pkt('object-format=sha1\n'),
          pktFlush(),
        ]);
        res.writeHead(200, { 'content-type': 'application/x-git-upload-pack-advertisement', 'content-length': body.length, 'x-github-request-id': `req-${(++reqCounter).toString(36)}-${Date.now().toString(36)}` });
        res.end(body);
        return true;
      }
      sendAdvertisement(res, 'git-upload-pack', refLinesV0(repo, UPLOAD_CAPS_V0), 'application/x-git-upload-pack-advertisement');
      return true;
    }
    if (service === 'git-receive-pack') {
      sendAdvertisement(res, 'git-receive-pack', refLinesV0(repo, RECEIVE_CAPS), 'application/x-git-receive-pack-advertisement');
      return true;
    }
    sendErr(res, 400, 'service is required');
    return true;
  }
  if (method !== 'POST') { sendErr(res, 405, 'Method Not Allowed'); return true; }
  if (!repo) { sendErr(res, 404, 'Not Found'); return true; }
  const raw = await readBody(req);

  if (action === 'git-upload-pack') {
    try {
      const { lines } = parsePktLines(raw);
      const first = lines[0]?.kind === 'data' ? lines[0].data.toString('utf8') : '';
      if (first.startsWith('command=')) {
        const cmd = first.slice('command='.length).trim();
        if (cmd === 'ls-refs') return handleLsRefs(res, repo, lines);
        if (cmd === 'fetch') return handleFetchV2(res, repo, lines);
        sendErr(res, 400, `unknown command ${cmd}`);
        return true;
      }
      return handleFetchV0(res, repo, lines);
    } catch {
      sendErr(res, 400, 'malformed pkt-line stream');
      return true;
    }
  }
  if (action === 'git-receive-pack') {
    try {
      return handleReceivePack(res, repo, raw);
    } catch {
      sendErr(res, 400, 'malformed push');
      return true;
    }
  }
  return false;
}
function handleLsRefs(res: ServerResponse, repo: Repo, lines: PktLine[]): boolean {
  let peel = false;
  let symrefs = false;
  let unborn = false;
  const prefixes: string[] = [];
  for (const l of lines) {
    if (l.kind !== 'data') continue;
    const s = l.data.toString('utf8').trim();
    if (s === 'peel') peel = true;
    else if (s === 'symrefs') symrefs = true;
    else if (s === 'unborn') unborn = true;
    else if (s.startsWith('ref-prefix ')) prefixes.push(s.slice('ref-prefix '.length));
  }
  const out: Buffer[] = [];
  const refs = sortedRefs(repo);
  const main = repo.refs.get('refs/heads/main');
  const matches = (ref: string): boolean => prefixes.length === 0 || prefixes.some((p) => ref.startsWith(p));
  if (refs.length === 0) {
    if (unborn && matches('HEAD')) out.push(pkt('unborn HEAD symref-target:refs/heads/main\n'));
  } else {
    if (matches('HEAD') && prefixes.length === 0) {
      out.push(pkt(`${main ?? refs[0]!.oid} HEAD${symrefs ? ' symref-target:refs/heads/main' : ''}\n`));
    }
    for (const r of refs) {
      if (!matches(r.ref)) continue;
      let line = `${r.oid} ${r.ref}`;
      if (peel && isTagObject(r.oid)) {
        const target = tagTarget(r.oid);
        if (target) line += ` peeled:${target}`;
      }
      out.push(pkt(`${line}\n`));
    }
  }
  const body = Buffer.concat([...out, pktFlush()]);
  res.writeHead(200, { 'content-type': 'application/x-git-upload-pack-result', 'content-length': body.length, 'x-github-request-id': `req-${(++reqCounter).toString(36)}-${Date.now().toString(36)}` });
  res.end(body);
  return true;
}
interface FetchReq { wants: string[]; haves: string[]; shallow: string[]; deepen: number | null; }
function parseFetchLines(lines: PktLine[]): FetchReq {
  const req: FetchReq = { wants: [], haves: [], shallow: [], deepen: null };
  for (const l of lines) {
    if (l.kind !== 'data') continue;
    const s = l.data.toString('utf8').trim();
    if (s.startsWith('want ')) req.wants.push(s.slice(5, 45));
    else if (s.startsWith('have ')) req.haves.push(s.slice(5, 45));
    else if (s.startsWith('shallow ')) req.shallow.push(s.slice(8, 48));
    else if (s.startsWith('deepen ')) { const n = Number(s.slice(7).trim()); if (Number.isFinite(n)) req.deepen = n; }
  }
  return req;
}
function computeFetchPack(repo: Repo, req: FetchReq): { oids: string[]; shallowOut: string[]; unshallowOut: string[] } {
  const stopAt = new Set(req.shallow);
  const maxDepth = req.deepen !== null ? req.deepen - 1 : -1;
  // Commit set within the depth limit.
  const wanted = reachableObjects(req.wants, maxDepth, new Set());
  // Objects the client already has: full closure of haves, stopping parent
  // traversal at the client's shallow boundaries.
  const haveObjs = req.haves.length > 0 ? reachableObjects(req.haves, -1, stopAt) : new Set<string>();
  const send = new Set<string>();
  for (const o of wanted) if (!haveObjs.has(o)) send.add(o);
  // Shallow-info: the frontier commits of the depth-limited walk, plus
  // unshallow for input boundaries whose parent is now included.
  const shallowOut: string[] = [];
  const unshallowOut: string[] = [];
  if (req.deepen !== null) {
    const frontier = new Set<string>();
    const seen = new Set<string>();
    const queue: Array<{ oid: string; depth: number }> = req.wants.map((oid) => ({ oid, depth: 0 }));
    let qi = 0;
    while (qi < queue.length) {
      const cur = queue[qi++]!;
      if (seen.has(cur.oid)) continue;
      const cv = parseCommitCached(cur.oid);
      if (!cv) continue;
      seen.add(cur.oid);
      if (cur.depth >= req.deepen! - 1) { frontier.add(cur.oid); continue; }
      for (const p of cv.parents) queue.push({ oid: p, depth: cur.depth + 1 });
    }
    for (const f of frontier) shallowOut.push(f);
    for (const s of req.shallow) {
      const obj = objects.get(s);
      if (!obj || obj.type !== 'commit') continue;
      const parents = parseCommit(obj.data).parents;
      if (parents.some((p) => seen.has(p) || frontier.has(p))) unshallowOut.push(s);
    }
  } else if (req.shallow.length > 0) {
    for (const s of req.shallow) shallowOut.push(s);
  }
  return { oids: [...send], shallowOut, unshallowOut };
}
// Packs are content-addressed, so a pack for a given oid set is immutable
// and safe to cache; the clone workload fetches the same tip 50x per round.
const packCache = new Map<string, Buffer>();
function cachedPack(oids: string[]): Buffer {
  const key = [...oids].sort().join(',');
  const hit = packCache.get(key);
  if (hit) return hit;
  const pack = writePack(oids);
  if (packCache.size > 256) packCache.clear();
  packCache.set(key, pack);
  return pack;
}
function handleFetchV2(res: ServerResponse, repo: Repo, lines: PktLine[]): boolean {
  const req = parseFetchLines(lines);
  const { oids, shallowOut, unshallowOut } = computeFetchPack(repo, req);
  const pack = cachedPack(oids);
  const parts: Buffer[] = [pkt('acknowledgments\n'), pkt('NAK\n'), pktDelim()];
  if (shallowOut.length > 0 || unshallowOut.length > 0) {
    parts.push(pkt('shallow-info\n'));
    for (const s of shallowOut) parts.push(pkt(`shallow ${s}\n`));
    for (const s of unshallowOut) parts.push(pkt(`unshallow ${s}\n`));
    parts.push(pktDelim());
  }
  parts.push(pkt('packfile\n'));
  parts.push(sidebandPack(pack));
  parts.push(pktFlush());
  const body = Buffer.concat(parts);
  res.writeHead(200, { 'content-type': 'application/x-git-upload-pack-result', 'content-length': body.length, 'x-github-request-id': `req-${(++reqCounter).toString(36)}-${Date.now().toString(36)}` });
  res.end(body);
  return true;
}
function handleFetchV0(res: ServerResponse, repo: Repo, lines: PktLine[]): boolean {
  // v0 request: wants section, flush, haves+done section, flush. The first
  // want line may carry capabilities after the oid.
  const req = parseFetchLines(lines);
  const { oids, shallowOut, unshallowOut } = computeFetchPack(repo, req);
  const pack = cachedPack(oids);
  const parts: Buffer[] = [];
  for (const s of shallowOut) parts.push(pkt(`shallow ${s}\n`));
  for (const s of unshallowOut) parts.push(pkt(`unshallow ${s}\n`));
  parts.push(pkt('NAK\n'));
  parts.push(sidebandPack(pack));
  parts.push(pktFlush());
  const body = Buffer.concat(parts);
  res.writeHead(200, { 'content-type': 'application/x-git-upload-pack-result', 'content-length': body.length, 'x-github-request-id': `req-${(++reqCounter).toString(36)}-${Date.now().toString(36)}` });
  res.end(body);
  return true;
}
function handleReceivePack(res: ServerResponse, repo: Repo, raw: Buffer): boolean {
  // Parse command pkt-lines up to the first flush; the raw pack follows it
  // immediately (parsePktLines would choke on the pack's 'PACK' magic).
  const commands: Array<{ old: string; new: string; ref: string }> = [];
  let off = 0;
  let rest = Buffer.alloc(0);
  while (off + 4 <= raw.length) {
    const len = parseInt(raw.toString('ascii', off, off + 4), 16);
    if (Number.isNaN(len)) throw new Error('bad pkt-line length');
    if (len === 0) { off += 4; rest = raw.subarray(off); break; }
    if (len < 4) throw new Error('bad pkt-line length');
    if (off + len > raw.length) throw new Error('truncated pkt-line');
    let s = raw.toString('utf8', off + 4, off + len);
    const nul = s.indexOf('\0');
    if (nul >= 0) s = s.slice(0, nul);
    const parts = s.trim().split(' ');
    if (parts.length >= 3) commands.push({ old: parts[0]!, new: parts[1]!, ref: parts[2]! });
    off += len;
  }
  if (rest.length > 0) {
    const objs = readPack(rest);
    for (const o of objs) storeObject(o.type, o.data);
  }
  const results: Array<{ ref: string; ok: boolean; reason?: string }> = [];
  for (const cmd of commands) {
    const current = repo.refs.get(cmd.ref);
    let ok = false;
    let reason = 'non-fast-forward';
    if (cmd.new === ZERO_OID) {
      // delete
      if (current !== undefined && cmd.old === current) { repo.refs.delete(cmd.ref); ok = true; }
    } else if (cmd.old === ZERO_OID) {
      // create
      if (current === undefined && objects.has(cmd.new)) { repo.refs.set(cmd.ref, cmd.new); ok = true; }
    } else if (current !== undefined && cmd.old === current) {
      if (cmd.ref.startsWith('refs/tags/')) { repo.refs.set(cmd.ref, cmd.new); ok = true; }
      else if (isAncestor(cmd.old, cmd.new)) { repo.refs.set(cmd.ref, cmd.new); ok = true; }
    }
    results.push({ ref: cmd.ref, ok, ...(ok ? {} : { reason }) });
  }
  repo.updated_at = nowIso();
  const innerParts: Buffer[] = [pkt('unpack ok\n')];
  for (const r of results) {
    innerParts.push(pkt(r.ok ? `ok ${r.ref}\n` : `ng ${r.ref} ${r.reason ?? 'non-fast-forward'}\n`));
  }
  innerParts.push(pktFlush());
  const inner = Buffer.concat(innerParts);
  const outer = Buffer.concat([sidebandPack(inner), pktFlush()]);
  res.writeHead(200, { 'content-type': 'application/x-git-receive-pack-result', 'content-length': outer.length, 'x-github-request-id': `req-${(++reqCounter).toString(36)}-${Date.now().toString(36)}` });
  res.end(outer);
  return true;
}

// ---------------------------------------------------------------- app
export function createApp(): Server {
  return createServer((req: IncomingMessage, res: ServerResponse) => {
    void (async () => {
      try {
        const path = pathOf(req);
        const method = req.method ?? 'GET';
        if (method === 'GET' && path === '/healthz') {
          sendJson(res, 200, { ok: true });
          return;
        }
        if (await handleGraphQL(req, res)) return;
        if (await handleMcp(req, res)) return;
        if (path.startsWith('/api/v3')) {
          await handleRest(req, res);
          return;
        }
        if (await handleGit(req, res)) return;
        sendErr(res, 404, 'Not Found');
      } catch (err) {
        if (!res.headersSent) sendErr(res, 500, err instanceof Error ? err.message : 'Internal Server Error');
        else { try { res.end(); } catch { /* ignore */ } }
      }
    })();
  });
}
