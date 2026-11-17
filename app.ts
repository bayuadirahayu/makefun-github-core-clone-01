// github-core-clone-01 entry: a GitHub-compatible git forge in one process.
// Surfaces: git smart HTTP (v2 + v0), REST v3, GraphQL v4, MCP (Streamable HTTP).
// Store: in-memory only. Deterministic: no wall clock, no randomness, no port/date
// in stored state (server commit timestamps come from a monotonic counter off a fixed base).

import { createServer as createTcpServer, type Server as TcpServer, type Socket } from 'node:net';
import type { IncomingMessage, ServerResponse } from 'node:http';
import { createHash } from 'node:crypto';
import { deflateSync, inflateSync } from 'node:zlib';

// ---------------------------------------------------------------------------
// constants
// ---------------------------------------------------------------------------

/** The scenario's viewer: wire.ts SCENARIO_SEED 0x6a09e667f3bcc909 builds this login. */
const VIEWER_LOGIN = 'adaiversen';
const VIEWER_ID = 1000;
const VIEWER_EMAIL = 'adaiversen@example.invalid';
const VIEWER_NAME = 'ada iversen';
const ZERO_OID = '0'.repeat(40);
const DEFAULT_BRANCH = 'main';
const FIXED_TS = '2026-01-01T00:00:00Z';
const COMMIT_EPOCH = 1700000000;
const JSON_TYPE = 'application/json; charset=utf-8';
const FORGE_NAME = 'forge';
const FORGE_VERSION = '1.0.0';

const TOKEN = process.env.MAKEFUN_SHOP_TOKEN ?? '';

// ---------------------------------------------------------------------------
// small utilities
// ---------------------------------------------------------------------------

function sha1Hex(data: Uint8Array): string {
  return createHash('sha1').update(data).digest('hex');
}

function b64encode(text: string): string {
  return Buffer.from(text, 'utf8').toString('base64');
}

function b64decodeLoose(content: string): string {
  return Buffer.from(content.replace(/[\r\n\t ]+/g, ''), 'base64').toString('utf8');
}

function isHex40(value: unknown): value is string {
  return typeof value === 'string' && /^[0-9a-f]{40}$/.test(value);
}

function asRecord(value: unknown): Record<string, unknown> | null {
  return value !== null && typeof value === 'object' && !Array.isArray(value) ? (value as Record<string, unknown>) : null;
}

function strField(value: Record<string, unknown>, key: string): string {
  const v = value[key];
  return typeof v === 'string' ? v : '';
}

function numField(value: Record<string, unknown>, key: string): number {
  const v = value[key];
  return typeof v === 'number' ? v : NaN;
}

// ---------------------------------------------------------------------------
// git object model
// ---------------------------------------------------------------------------

type GitObjectType = 'commit' | 'tree' | 'blob' | 'tag';

interface GitObject {
  type: GitObjectType;
  data: Buffer;
}

const TYPE_CODE: Record<GitObjectType, number> = { commit: 1, tree: 2, blob: 3, tag: 4 };
const CODE_TYPE: Record<number, GitObjectType> = { 1: 'commit', 2: 'tree', 3: 'blob', 4: 'tag' };

function hashObject(type: GitObjectType, data: Uint8Array): string {
  const body = Buffer.isBuffer(data) ? data : Buffer.from(data);
  const hash = createHash('sha1');
  hash.update(Buffer.from(`${type} ${body.length}\0`, 'utf8'));
  hash.update(body);
  return hash.digest('hex');
}

interface TreeEntry {
  mode: string;
  name: string;
  oid: string;
}

function parseTree(data: Uint8Array): TreeEntry[] {
  const buffer = Buffer.isBuffer(data) ? data : Buffer.from(data);
  const entries: TreeEntry[] = [];
  let offset = 0;
  while (offset < buffer.length) {
    const space = buffer.indexOf(0x20, offset);
    if (space < 0) throw new Error('tree entry has no mode separator');
    const nul = buffer.indexOf(0x00, space + 1);
    if (nul < 0) throw new Error('tree entry has no name terminator');
    if (nul + 21 > buffer.length) throw new Error('tree entry has a truncated object id');
    entries.push({
      mode: buffer.subarray(offset, space).toString('ascii'),
      name: buffer.subarray(space + 1, nul).toString('utf8'),
      oid: buffer.subarray(nul + 1, nul + 21).toString('hex'),
    });
    offset = nul + 21;
  }
  return entries;
}

function compareTreeNames(a: { name: string; mode: string }, b: { name: string; mode: string }): number {
  const left = Buffer.from(a.mode === '40000' ? `${a.name}/` : a.name, 'utf8');
  const right = Buffer.from(b.mode === '40000' ? `${b.name}/` : b.name, 'utf8');
  return Buffer.compare(left, right);
}

function buildTree(entries: readonly TreeEntry[]): Buffer {
  const sorted = [...entries].sort(compareTreeNames);
  const parts: Buffer[] = [];
  for (const entry of sorted) {
    parts.push(Buffer.from(`${entry.mode} ${entry.name}\0`, 'utf8'));
    parts.push(Buffer.from(entry.oid, 'hex'));
  }
  return Buffer.concat(parts);
}

interface CommitView {
  tree: string;
  parents: string[];
  author: string;
  committer: string;
  message: string;
}

function parseCommit(data: Uint8Array): CommitView {
  const buffer = Buffer.isBuffer(data) ? data : Buffer.from(data);
  const blank = buffer.indexOf('\n\n');
  const headerEnd = blank < 0 ? buffer.length : blank;
  const message = blank < 0 ? '' : buffer.subarray(blank + 2).toString('utf8').replace(/\n+$/, '');
  let tree = '';
  const parents: string[] = [];
  let author = '';
  let committer = '';
  for (const line of buffer.subarray(0, headerEnd).toString('utf8').split('\n')) {
    if (!line) continue;
    const space = line.indexOf(' ');
    const key = space < 0 ? line : line.slice(0, space);
    const value = space < 0 ? '' : line.slice(space + 1);
    if (key === 'tree') tree = value;
    else if (key === 'parent') parents.push(value);
    else if (key === 'author') author = value;
    else if (key === 'committer') committer = value;
  }
  return { tree, parents, author, committer, message };
}

function parseTag(data: Uint8Array): { object: string; type: GitObjectType; tag: string; tagger: string; message: string } {
  const buffer = Buffer.isBuffer(data) ? data : Buffer.from(data);
  const blank = buffer.indexOf('\n\n');
  const headerEnd = blank < 0 ? buffer.length : blank;
  const headers = new Map<string, string>();
  for (const line of buffer.subarray(0, headerEnd).toString('utf8').split('\n')) {
    if (!line) continue;
    const space = line.indexOf(' ');
    if (space < 0) continue;
    headers.set(line.slice(0, space), line.slice(space + 1));
  }
  const type = headers.get('type') ?? '';
  return {
    object: headers.get('object') ?? '',
    type: (type === 'commit' || type === 'tree' || type === 'blob' || type === 'tag' ? type : 'commit') as GitObjectType,
    tag: headers.get('tag') ?? '',
    tagger: headers.get('tagger') ?? '',
    message: blank < 0 ? '' : buffer.subarray(blank + 2).toString('utf8'),
  };
}

/** Every object reachable from `roots` (tags followed, gitlinks skipped). */
function collectReachable(roots: Iterable<string>, lookup: (oid: string) => GitObject | undefined): Set<string> {
  const seen = new Set<string>();
  const queue: string[] = [];
  for (const root of roots) if (isHex40(root)) queue.push(root);
  while (queue.length) {
    const oid = queue.pop()!;
    if (seen.has(oid)) continue;
    const object = lookup(oid);
    if (!object) continue;
    seen.add(oid);
    if (object.type === 'commit') {
      const commit = parseCommit(object.data);
      queue.push(commit.tree);
      for (const parent of commit.parents) queue.push(parent);
    } else if (object.type === 'tag') {
      queue.push(parseTag(object.data).object);
    } else if (object.type === 'tree') {
      for (const entry of parseTree(object.data)) {
        if (entry.mode === '160000') continue;
        queue.push(entry.oid);
      }
    }
  }
  return seen;
}

// ---------------------------------------------------------------------------
// pkt-line codec
// ---------------------------------------------------------------------------

const PKT_LINE_MAX = 65520;

function encodePktLine(payload: string | Uint8Array): Buffer {
  const data = typeof payload === 'string' ? Buffer.from(payload, 'utf8') : payload;
  if (data.length > PKT_LINE_MAX - 4) throw new Error('pkt-line payload too long');
  const header = Buffer.allocUnsafe(4);
  header.write((data.length + 4).toString(16).padStart(4, '0'), 0, 4, 'ascii');
  return Buffer.concat([header, data]);
}

const PKT_FLUSH = Buffer.from('0000', 'ascii');
const PKT_DELIM = Buffer.from('0001', 'ascii');

type PktItem = { kind: 'data'; payload: Buffer } | { kind: 'flush' } | { kind: 'delim' } | { kind: 'response-end' };

/**
 * Parse pkt-lines from `buf` starting at `offset`. Returns the packets and the offset just
 * past the last parsed packet (the raw pack bytes follow a flush in receive-pack).
 */
function parsePktLines(buf: Buffer, offset = 0): { packets: PktItem[]; next: number } {
  const packets: PktItem[] = [];
  let at = offset;
  while (at + 4 <= buf.length) {
    const header = buf.subarray(at, at + 4).toString('ascii');
    if (!/^[0-9a-fA-F]{4}$/.test(header)) break;
    const length = Number.parseInt(header, 16);
    if (length === 0) {
      packets.push({ kind: 'flush' });
      at += 4;
      continue;
    }
    if (length === 1) {
      packets.push({ kind: 'delim' });
      at += 4;
      continue;
    }
    if (length === 2) {
      packets.push({ kind: 'response-end' });
      at += 4;
      continue;
    }
    if (length < 4 || length > PKT_LINE_MAX || at + length > buf.length) break;
    packets.push({ kind: 'data', payload: buf.subarray(at + 4, at + length) });
    at += length;
  }
  return { packets, next: at };
}

function pktLinesText(packets: readonly PktItem[]): string[] {
  const lines: string[] = [];
  for (const packet of packets) if (packet.kind === 'data') lines.push(packet.payload.toString('utf8'));
  return lines;
}

// ---------------------------------------------------------------------------
// packfile read/write
// ---------------------------------------------------------------------------

function inflateAt(buffer: Buffer, offset: number): { data: Buffer; next: number } {
  const result = inflateSync(buffer.subarray(offset), { info: true }) as unknown as {
    buffer: Buffer;
    engine: { bytesWritten: number };
  };
  const written = result.engine.bytesWritten;
  if (!written || written <= 0) throw new Error(`zlib stream at offset ${offset} consumed no bytes`);
  return { data: result.buffer, next: offset + written };
}

function applyDelta(base: Uint8Array, delta: Uint8Array): Buffer {
  const baseBuffer = Buffer.isBuffer(base) ? base : Buffer.from(base);
  const deltaBuffer = Buffer.isBuffer(delta) ? delta : Buffer.from(delta);
  let offset = 0;
  const readSize = (): number => {
    let value = 0;
    let shift = 0;
    for (;;) {
      if (offset >= deltaBuffer.length) throw new Error('delta size varint truncated');
      const byte = deltaBuffer[offset++];
      value += (byte & 0x7f) * 2 ** shift;
      shift += 7;
      if (!(byte & 0x80)) break;
    }
    return value;
  };
  const sourceSize = readSize();
  const targetSize = readSize();
  if (sourceSize !== baseBuffer.length) throw new Error('delta expects a different base size');
  const out = Buffer.allocUnsafe(targetSize);
  let written = 0;
  while (offset < deltaBuffer.length) {
    const op = deltaBuffer[offset++];
    if (op & 0x80) {
      let copyOffset = 0;
      let copySize = 0;
      let shift = 0;
      for (let bit = 0; bit < 4; bit += 1) {
        if (op & (1 << bit)) copyOffset += deltaBuffer[offset++] * 2 ** shift;
        shift += 8;
      }
      shift = 0;
      for (let bit = 4; bit < 7; bit += 1) {
        if (op & (1 << bit)) copySize += deltaBuffer[offset++] * 2 ** shift;
        shift += 8;
      }
      if (copySize === 0) copySize = 0x10000;
      if (copyOffset + copySize > baseBuffer.length) throw new Error('delta copy out of base');
      baseBuffer.copy(out, written, copyOffset, copyOffset + copySize);
      written += copySize;
    } else if (op !== 0) {
      const literal = op & 0x7f;
      deltaBuffer.copy(out, written, offset, offset + literal);
      offset += literal;
      written += literal;
    } else {
      throw new Error('delta opcode 0 invalid');
    }
  }
  if (written !== targetSize) throw new Error('delta produced the wrong size');
  return out;
}

function readVarintSize(buffer: Buffer, start: number): { size: number; next: number; first: number } {
  let byte = buffer[start];
  const first = byte;
  let size = byte & 0x0f;
  let shift = 4;
  let offset = start + 1;
  while (byte & 0x80) {
    byte = buffer[offset++];
    size += (byte & 0x7f) * 2 ** shift;
    shift += 7;
  }
  return { size, next: offset, first };
}

function readOfsDeltaBase(buffer: Buffer, start: number): { baseOffset: number; next: number } {
  let byte = buffer[start];
  let offset = start + 1;
  let value = byte & 0x7f;
  while (byte & 0x80) {
    byte = buffer[offset++];
    value = (value + 1) * 128 + (byte & 0x7f);
  }
  return { baseOffset: value, next: offset };
}

/** Parse a packfile (v2/v3, plain + OFS/REF deltas) into resolved objects. */
function readPack(pack: Uint8Array, resolveBase?: (oid: string) => GitObject | undefined): Map<string, GitObject> {
  const buffer = Buffer.isBuffer(pack) ? pack : Buffer.from(pack);
  if (buffer.length < 32) throw new Error('pack too short');
  if (buffer.subarray(0, 4).toString('ascii') !== 'PACK') throw new Error('pack does not start with PACK');
  const version = buffer.readUInt32BE(4);
  if (version !== 2 && version !== 3) throw new Error(`unsupported pack version ${version}`);
  const declaredCount = buffer.readUInt32BE(8);
  const trailerStart = buffer.length - 20;
  const trailer = buffer.subarray(trailerStart).toString('hex');
  const computed = sha1Hex(buffer.subarray(0, trailerStart));
  if (trailer !== computed) throw new Error('pack trailer checksum mismatch');

  interface RawEntry {
    offset: number;
    typeCode: number;
    size: number;
    data: Buffer;
    baseOffset?: number;
    baseOid?: string;
    resolvedType?: GitObjectType;
    resolved?: Buffer;
    oid?: string;
  }
  const raw: RawEntry[] = [];
  const byOffset = new Map<number, RawEntry>();
  let offset = 12;
  for (let index = 0; index < declaredCount; index += 1) {
    const entryOffset = offset;
    const header = readVarintSize(buffer, offset);
    offset = header.next;
    const typeCode = (header.first >> 4) & 0x07;
    const entry: RawEntry = { offset: entryOffset, typeCode, size: header.size, data: Buffer.alloc(0) };
    if (typeCode === 6) {
      const base = readOfsDeltaBase(buffer, offset);
      offset = base.next;
      entry.baseOffset = entryOffset - base.baseOffset;
    } else if (typeCode === 7) {
      entry.baseOid = buffer.subarray(offset, offset + 20).toString('hex');
      offset += 20;
    } else if (!CODE_TYPE[typeCode]) {
      throw new Error(`pack entry ${index} has unknown type code ${typeCode}`);
    }
    const inflated = inflateAt(buffer.subarray(0, trailerStart), offset);
    if (inflated.data.length !== header.size) throw new Error('pack entry size mismatch');
    entry.data = inflated.data;
    offset = inflated.next;
    raw.push(entry);
    byOffset.set(entryOffset, entry);
  }

  const objects = new Map<string, GitObject>();
  const resolvedByOid = new Map<string, RawEntry>();
  const resolving = new Set<number>();
  const resolve = (entry: RawEntry): { type: GitObjectType; data: Buffer; oid: string } => {
    if (entry.resolved && entry.resolvedType && entry.oid) {
      return { type: entry.resolvedType, data: entry.resolved, oid: entry.oid };
    }
    if (resolving.has(entry.offset)) throw new Error('delta cycle in pack');
    resolving.add(entry.offset);
    let type: GitObjectType;
    let data: Buffer;
    if (entry.typeCode === 6) {
      const baseEntry = byOffset.get(entry.baseOffset!);
      if (!baseEntry) throw new Error('ofs-delta base not in pack');
      const base = resolve(baseEntry);
      type = base.type;
      data = applyDelta(base.data, entry.data);
    } else if (entry.typeCode === 7) {
      const baseEntry = resolvedByOid.get(entry.baseOid!);
      if (baseEntry) {
        const base = resolve(baseEntry);
        type = base.type;
        data = applyDelta(base.data, entry.data);
      } else {
        const external = resolveBase?.(entry.baseOid!);
        if (!external) throw new Error(`ref-delta base ${entry.baseOid} not supplied`);
        type = external.type;
        data = applyDelta(external.data, entry.data);
      }
    } else {
      type = CODE_TYPE[entry.typeCode];
      data = entry.data;
    }
    const oid = hashObject(type, data);
    entry.resolved = data;
    entry.resolvedType = type;
    entry.oid = oid;
    resolvedByOid.set(oid, entry);
    resolving.delete(entry.offset);
    return { type, data, oid };
  };
  for (const entry of raw) {
    const resolved = resolve(entry);
    if (!objects.has(resolved.oid)) objects.set(resolved.oid, { type: resolved.type, data: resolved.data });
  }
  return objects;
}

function writePackObjectHeader(type: GitObjectType, size: number): Buffer {
  const code = TYPE_CODE[type];
  const bytes: number[] = [];
  let remaining = size;
  let first = (code << 4) | (remaining & 0x0f);
  remaining = Math.floor(remaining / 16);
  while (remaining > 0) {
    bytes.push(first | 0x80);
    first = remaining & 0x7f;
    remaining = Math.floor(remaining / 128);
  }
  bytes.push(first);
  return Buffer.from(bytes);
}

/** Build a packfile from plain objects (no deltas). */
function writePack(objects: Iterable<GitObject>): Buffer {
  const list = [...objects];
  const parts: Buffer[] = [];
  const header = Buffer.allocUnsafe(12);
  header.write('PACK', 0, 4, 'ascii');
  header.writeUInt32BE(2, 4);
  header.writeUInt32BE(list.length, 8);
  parts.push(header);
  for (const object of list) {
    parts.push(writePackObjectHeader(object.type, object.data.length));
    parts.push(deflateSync(object.data));
  }
  const body = Buffer.concat(parts);
  return Buffer.concat([body, createHash('sha1').update(body).digest()]);
}

// ---------------------------------------------------------------------------
// store
// ---------------------------------------------------------------------------

interface Label {
  name: string;
  color: string;
}

interface Issue {
  id: number;
  number: number;
  title: string;
  body: string;
  state: 'open' | 'closed';
  labels: Label[];
  seq: number;
}

interface IssueComment {
  id: number;
  body: string;
}

interface Pull {
  id: number;
  number: number;
  title: string;
  body: string;
  state: 'open' | 'closed';
  headRef: string;
  baseRef: string;
  headSha: string;
  baseSha: string;
  merged: boolean;
  mergedAt: string | null;
  mergeCommitSha: string | null;
  seq: number;
}

interface Repo {
  id: number;
  name: string;
  owner: string;
  description: string;
  private: boolean;
  defaultBranch: string;
  objects: Map<string, GitObject>;
  refs: Map<string, string>;
  issues: Issue[];
  nextIssue: number;
  pulls: Pull[];
  nextPull: number;
  labels: Map<string, Label>;
  comments: Map<number, IssueComment[]>;
  nextComment: number;
  commitSeq: Map<string, number>;
}

const repos = new Map<string, Repo>();
let nextRepoId = 1;
let nextIssueId = 1;
let nextPullId = 1;
let nextCommitSeq = 1;
let commitClock = 0;
let requestCounter = 0;

function repoKey(owner: string, name: string): string {
  return `${owner}/${name}`;
}

function createRepo(name: string, description: string, isPrivate: boolean): Repo {
  const repo: Repo = {
    id: nextRepoId++,
    name,
    owner: VIEWER_LOGIN,
    description,
    private: isPrivate,
    defaultBranch: DEFAULT_BRANCH,
    objects: new Map(),
    refs: new Map(),
    issues: [],
    nextIssue: 1,
    pulls: [],
    nextPull: 1,
    labels: new Map(),
    comments: new Map(),
    nextComment: 1,
    commitSeq: new Map(),
  };
  repos.set(repoKey(VIEWER_LOGIN, name), repo);
  return repo;
}

function findRepo(owner: string, name: string): Repo | null {
  if (owner !== VIEWER_LOGIN) return null;
  return repos.get(repoKey(owner, name)) ?? null;
}

function storeObject(repo: Repo, type: GitObjectType, data: Buffer): string {
  const oid = hashObject(type, data);
  if (!repo.objects.has(oid)) repo.objects.set(oid, { type, data });
  if (type === 'commit' && !repo.commitSeq.has(oid)) repo.commitSeq.set(oid, nextCommitSeq++);
  return oid;
}

function getObject(repo: Repo, oid: string): GitObject | undefined {
  return repo.objects.get(oid);
}

/** Peel a tag (recursively) to its target object id. */
function peelToCommit(repo: Repo, oid: string): string | null {
  let current = oid;
  const seen = new Set<string>();
  for (;;) {
    if (seen.has(current)) return null;
    seen.add(current);
    const object = repo.objects.get(current);
    if (!object) return null;
    if (object.type === 'commit') return current;
    if (object.type === 'tag') {
      current = parseTag(object.data).object;
      continue;
    }
    return null;
  }
}

/** True when `ancestor` is reachable from `descendant` (or equal), via commit parents. */
function isAncestor(repo: Repo, ancestor: string, descendant: string): boolean {
  if (ancestor === descendant) return true;
  const ancCommit = peelToCommit(repo, ancestor);
  const descCommit = peelToCommit(repo, descendant);
  if (ancCommit === null || descCommit === null) return false;
  if (ancCommit === descCommit) return true;
  const seen = new Set<string>();
  const queue: string[] = [descCommit];
  while (queue.length) {
    const oid = queue.pop()!;
    if (seen.has(oid)) continue;
    seen.add(oid);
    const object = repo.objects.get(oid);
    if (!object || object.type !== 'commit') continue;
    for (const parent of parseCommit(object.data).parents) {
      if (parent === ancCommit) return true;
      queue.push(parent);
    }
  }
  return false;
}

/** The merge-base of two commits (first common ancestor found walking from `b`). */
function mergeBase(repo: Repo, a: string, b: string): string | null {
  const aCommit = peelToCommit(repo, a);
  const bCommit = peelToCommit(repo, b);
  if (aCommit === null || bCommit === null) return null;
  const ancestorsA = new Set<string>();
  const queueA: string[] = [aCommit];
  while (queueA.length) {
    const oid = queueA.pop()!;
    if (ancestorsA.has(oid)) continue;
    ancestorsA.add(oid);
    const object = repo.objects.get(oid);
    if (!object || object.type !== 'commit') continue;
    for (const parent of parseCommit(object.data).parents) queueA.push(parent);
  }
  const queueB: string[] = [bCommit];
  const seenB = new Set<string>();
  while (queueB.length) {
    const oid = queueB.pop()!;
    if (seenB.has(oid)) continue;
    seenB.add(oid);
    if (ancestorsA.has(oid)) return oid;
    const object = repo.objects.get(oid);
    if (!object || object.type !== 'commit') continue;
    for (const parent of parseCommit(object.data).parents) queueB.push(parent);
  }
  return null;
}

/** All commits reachable from `tip`, newest first (by insertion order). */
function listCommits(repo: Repo, tip: string): { sha: string; commit: CommitView }[] {
  const reachable = collectReachable([tip], (oid) => repo.objects.get(oid));
  const commits: { sha: string; commit: CommitView; seq: number }[] = [];
  for (const oid of reachable) {
    const object = repo.objects.get(oid);
    if (object?.type === 'commit') {
      commits.push({ sha: oid, commit: parseCommit(object.data), seq: repo.commitSeq.get(oid) ?? 0 });
    }
  }
  commits.sort((x, y) => y.seq - x.seq);
  return commits.map(({ sha, commit }) => ({ sha, commit }));
}

/** Flatten a tree to path -> {oid, mode}. */
function flattenTree(repo: Repo, treeOid: string, prefix = '', out = new Map<string, { oid: string; mode: string }>()): Map<string, { oid: string; mode: string }> {
  const object = repo.objects.get(treeOid);
  if (!object || object.type !== 'tree') return out;
  for (const entry of parseTree(object.data)) {
    const path = prefix === '' ? entry.name : `${prefix}/${entry.name}`;
    if (entry.mode === '40000') flattenTree(repo, entry.oid, path, out);
    else if (entry.mode !== '160000') out.set(path, { oid: entry.oid, mode: entry.mode });
  }
  return out;
}

function treeOfCommit(repo: Repo, commitOid: string): string | null {
  const commit = peelToCommit(repo, commitOid);
  if (commit === null) return null;
  const object = repo.objects.get(commit);
  if (!object || object.type !== 'commit') return null;
  return parseCommit(object.data).tree;
}

/**
 * Set (or delete, when `blobOid` is null) `path` in the tree rooted at `rootTreeOid`
 * (null = empty tree). Returns the new root tree oid; intermediate trees are stored.
 */
function setPathInTree(repo: Repo, rootTreeOid: string | null, segments: string[], blobOid: string | null): string {
  const setIn = (treeOid: string | null, depth: number): string => {
    const entries = new Map<string, TreeEntry>();
    if (treeOid !== null) {
      const object = repo.objects.get(treeOid);
      if (object?.type === 'tree') {
        for (const entry of parseTree(object.data)) entries.set(entry.name, entry);
      }
    }
    const name = segments[depth]!;
    if (depth === segments.length - 1) {
      if (blobOid === null) entries.delete(name);
      else entries.set(name, { mode: '100644', name, oid: blobOid });
    } else {
      const child = entries.get(name);
      const childTree = child && child.mode === '40000' ? child.oid : null;
      const newChild = setIn(childTree, depth + 1);
      entries.set(name, { mode: '40000', name, oid: newChild });
    }
    const data = buildTree([...entries.values()]);
    return storeObject(repo, 'tree', data);
  };
  return setIn(rootTreeOid, 0);
}

/** Build a server commit object and store it. */
function createServerCommit(repo: Repo, treeOid: string, parents: string[], message: string): string {
  const ts = COMMIT_EPOCH + commitClock++;
  const who = `${VIEWER_NAME} <${VIEWER_EMAIL}> ${ts} +0000`;
  const lines = [`tree ${treeOid}`];
  for (const parent of parents) lines.push(`parent ${parent}`);
  lines.push(`author ${who}`, `committer ${who}`, '');
  const body = `${lines.join('\n')}\n${message.endsWith('\n') ? message : `${message}\n`}`;
  return storeObject(repo, 'commit', Buffer.from(body, 'utf8'));
}

/** Resolve a ref name or commit sha to a commit oid, or null. */
function resolveRef(repo: Repo, ref: string): string | null {
  const direct = repo.refs.get(`refs/heads/${ref}`);
  if (direct !== undefined) return direct;
  if (isHex40(ref)) {
    const object = repo.objects.get(ref);
    if (object?.type === 'commit') return ref;
    if (object?.type === 'tag') return peelToCommit(repo, ref);
  }
  const asRef = repo.refs.get(ref);
  if (asRef !== undefined) return asRef;
  return null;
}

interface FileChange {
  path: string;
  oldOid: string | null;
  newOid: string | null;
  status: 'added' | 'modified' | 'removed';
  additions: number;
  deletions: number;
  changes: number;
}

function countLines(text: string): string[] {
  if (text === '') return [];
  const lines = text.split('\n');
  if (lines.length > 0 && lines[lines.length - 1] === '') lines.pop();
  return lines;
}

/** LCS length table over two line arrays (files here are small). */
function lcsLength(a: string[], b: string[]): number {
  const rows = a.length + 1;
  const cols = b.length + 1;
  const dp = new Uint32Array(rows * cols);
  for (let i = 1; i < rows; i += 1) {
    for (let j = 1; j < cols; j += 1) {
      dp[i * cols + j] = a[i - 1] === b[j - 1] ? dp[(i - 1) * cols + (j - 1)] + 1 : Math.max(dp[(i - 1) * cols + j], dp[i * cols + (j - 1)]);
    }
  }
  return dp[a.length * cols + b.length] ?? 0;
}

function blobText(repo: Repo, oid: string | null): string {
  if (oid === null) return '';
  const object = repo.objects.get(oid);
  if (!object || object.type !== 'blob') return '';
  return object.data.toString('utf8');
}

/** Diff two trees (by oid) into per-file changes with line counts. */
function diffTrees(repo: Repo, baseTreeOid: string | null, headTreeOid: string | null): FileChange[] {
  const base = baseTreeOid === null ? new Map() : flattenTree(repo, baseTreeOid);
  const head = headTreeOid === null ? new Map() : flattenTree(repo, headTreeOid);
  const paths = new Set([...base.keys(), ...head.keys()]);
  const changes: FileChange[] = [];
  for (const path of [...paths].sort()) {
    const oldEntry = base.get(path);
    const newEntry = head.get(path);
    if (oldEntry?.oid === newEntry?.oid) continue;
    const oldOid = oldEntry?.oid ?? null;
    const newOid = newEntry?.oid ?? null;
    const status: FileChange['status'] = oldOid === null ? 'added' : newOid === null ? 'removed' : 'modified';
    const oldLines = countLines(blobText(repo, oldOid));
    const newLines = countLines(blobText(repo, newOid));
    const common = lcsLength(oldLines, newLines);
    const additions = newLines.length - common;
    const deletions = oldLines.length - common;
    changes.push({ path, oldOid, newOid, status, additions, deletions, changes: additions + deletions });
  }
  return changes;
}

/**
 * True when merging `headTip` into `baseTip` would conflict: both sides changed the same
 * path since the merge-base and ended with different contents.
 */
function mergeConflicts(repo: Repo, baseTip: string, headTip: string): boolean {
  const base = mergeBase(repo, baseTip, headTip);
  if (base === null) return true;
  const baseTree = treeOfCommit(repo, base);
  const headTree = treeOfCommit(repo, headTip);
  const currentTree = treeOfCommit(repo, baseTip);
  if (baseTree === null || headTree === null || currentTree === null) return true;
  const headChanges = diffTrees(repo, baseTree, headTree);
  const baseChanges = diffTrees(repo, baseTree, currentTree);
  const baseChanged = new Map(baseChanges.map((c) => [c.path, c.newOid]));
  for (const change of headChanges) {
    if (baseChanged.has(change.path) && baseChanged.get(change.path) !== change.newOid) return true;
  }
  return false;
}

/** The mergeable state GitHub reports for a pull request. */
function mergeableState(repo: Repo, pull: Pull): 'MERGEABLE' | 'CONFLICTING' | 'UNKNOWN' {
  if (pull.state !== 'open') return 'UNKNOWN';
  const baseTip = repo.refs.get(`refs/heads/${pull.baseRef}`);
  const headTip = repo.refs.get(`refs/heads/${pull.headRef}`);
  if (baseTip === undefined || headTip === undefined) return 'UNKNOWN';
  return mergeConflicts(repo, baseTip, headTip) ? 'CONFLICTING' : 'MERGEABLE';
}

// ---------------------------------------------------------------------------
// global ids (opaque, stable)
// ---------------------------------------------------------------------------

function encodeId(kind: string, value: string): string {
  return Buffer.from(`${kind}:${value}`, 'utf8').toString('base64url');
}

function decodeId(id: string): { kind: string; value: string } | null {
  try {
    const text = Buffer.from(id, 'base64url').toString('utf8');
    const colon = text.indexOf(':');
    if (colon <= 0) return null;
    return { kind: text.slice(0, colon), value: text.slice(colon + 1) };
  } catch {
    return null;
  }
}

function repoGlobalId(repo: Repo): string {
  return encodeId('R', `${repo.owner}/${repo.name}`);
}

function issueGlobalId(repo: Repo, issue: Issue): string {
  return encodeId('I', `${repo.owner}/${repo.name}:${issue.number}`);
}

function pullGlobalId(repo: Repo, pull: Pull): string {
  return encodeId('P', `${repo.owner}/${repo.name}:${pull.number}`);
}

function commentGlobalId(repo: Repo, issueNumber: number, comment: IssueComment): string {
  return encodeId('C', `${repo.owner}/${repo.name}:${issueNumber}:${comment.id}`);
}

// ---------------------------------------------------------------------------
// HTTP plumbing
// ---------------------------------------------------------------------------

class HttpError extends Error {
  status: number;
  constructor(status: number, message: string) {
    super(message);
    this.status = status;
  }
}

function sendJson(res: ServerResponse, status: number, body: unknown, extraHeaders: Record<string, string> = {}): void {
  const text = body === null || body === undefined ? '' : `${JSON.stringify(body)}\n`;
  res.writeHead(status, {
    'content-type': JSON_TYPE,
    'content-length': Buffer.byteLength(text),
    'x-github-request-id': `req-${++requestCounter}`,
    ...extraHeaders,
  });
  res.end(text);
}

function sendError(res: ServerResponse, status: number, message: string): void {
  sendJson(res, status, { message });
}

function authed(req: IncomingMessage): boolean {
  const header = req.headers.authorization ?? '';
  if (!header.startsWith('Bearer ')) return false;
  const token = header.slice(7);
  if (token === '') return false;
  if (TOKEN !== '' && token !== TOKEN) return false;
  return true;
}

function requireAuth(req: IncomingMessage, res: ServerResponse): boolean {
  if (authed(req)) return true;
  sendError(res, 401, 'Requires authentication');
  return false;
}

function readBody(req: IncomingMessage): Promise<Buffer> {
  // The transport already buffered the whole body before dispatching: take
  // it straight instead of replaying data/end events through a Promise.
  const pre = (req as unknown as { preBody?: Buffer }).preBody;
  if (pre !== undefined) return Promise.resolve(pre);
  return new Promise((resolve, reject) => {
    const chunks: Buffer[] = [];
    let size = 0;
    req.on('data', (chunk: Buffer) => {
      size += chunk.length;
      if (size > 64 * 1024 * 1024) {
        reject(new HttpError(413, 'request body too large'));
        req.destroy();
      } else {
        chunks.push(chunk);
      }
    });
    req.on('end', () => resolve(Buffer.concat(chunks)));
    req.on('error', (err) => reject(err));
  });
}

/** Parse a JSON request body; empty body is {}; malformed JSON is a 400. */
function parseJsonBody(raw: Buffer): Record<string, unknown> {
  const text = raw.toString('utf8').trim();
  if (text === '') return {};
  let value: unknown;
  try {
    value = JSON.parse(text);
  } catch {
    throw new HttpError(400, 'Problems parsing JSON');
  }
  const record = asRecord(value);
  if (record === null) throw new HttpError(400, 'Problems parsing JSON');
  return record;
}

function splitPath(pathname: string): string[] {
  return pathname.split('/').filter((part) => part !== '').map((part) => {
    // Most segments carry no escapes; decoding one is a wasted call.
    if (!part.includes('%')) return part;
    try {
      return decodeURIComponent(part);
    } catch {
      return part;
    }
  });
}

function pageParams(query: URLSearchParams): { page: number; perPage: number } {
  const page = Math.max(1, Number.parseInt(query.get('page') ?? '1', 10) || 1);
  let perPage = Number.parseInt(query.get('per_page') ?? '30', 10) || 30;
  perPage = Math.min(100, Math.max(1, perPage));
  return { page, perPage };
}

/** Slice `items` to one page and build the GitHub Link header (absolute URLs, same origin). */
function paginate<T>(req: IncomingMessage, pathname: string, query: URLSearchParams, items: readonly T[]): { page: T[]; link: string | null } {
  const { page, perPage } = pageParams(query);
  const totalPages = Math.max(1, Math.ceil(items.length / perPage));
  const start = (page - 1) * perPage;
  const slice = items.slice(start, start + perPage);
  const host = req.headers.host ?? 'localhost';
  const base = query.toString();
  const linkFor = (p: number): string => {
    const params = new URLSearchParams(base);
    params.set('page', String(p));
    params.set('per_page', String(perPage));
    return `http://${host}${pathname}?${params.toString()}`;
  };
  const parts: string[] = [];
  if (page > 1) {
    parts.push(`<${linkFor(1)}>; rel="first"`, `<${linkFor(page - 1)}>; rel="prev"`);
  }
  if (page < totalPages) {
    parts.push(`<${linkFor(page + 1)}>; rel="next"`, `<${linkFor(totalPages)}>; rel="last"`);
  }
  return { page: [...slice], link: parts.length ? parts.join(', ') : null };
}

// ---------------------------------------------------------------------------
// REST v3 shapes
// ---------------------------------------------------------------------------

let nextItemSeq = 1;

function repoJson(repo: Repo): Record<string, unknown> {
  return {
    id: repo.id,
    node_id: repoGlobalId(repo),
    name: repo.name,
    full_name: `${repo.owner}/${repo.name}`,
    owner: { login: repo.owner, id: VIEWER_ID, type: 'User' },
    private: repo.private,
    description: repo.description,
    default_branch: repo.defaultBranch,
    created_at: FIXED_TS,
    updated_at: FIXED_TS,
    html_url: `https://example.invalid/${repo.owner}/${repo.name}`,
    clone_url: `https://example.invalid/${repo.owner}/${repo.name}.git`,
    has_issues: true,
  };
}

function issueJson(repo: Repo, issue: Issue): Record<string, unknown> {
  return {
    id: issue.id,
    node_id: issueGlobalId(repo, issue),
    number: issue.number,
    title: issue.title,
    body: issue.body,
    state: issue.state,
    labels: issue.labels.map((label) => ({ name: label.name, color: label.color })),
    user: { login: VIEWER_LOGIN, id: VIEWER_ID, type: 'User' },
    created_at: FIXED_TS,
    updated_at: FIXED_TS,
  };
}

function pullJson(repo: Repo, pull: Pull): Record<string, unknown> {
  return {
    id: pull.id,
    node_id: pullGlobalId(repo, pull),
    number: pull.number,
    title: pull.title,
    body: pull.body,
    state: pull.state,
    head: { ref: pull.headRef, sha: pull.headSha, label: `${repo.owner}:${pull.headRef}` },
    base: { ref: pull.baseRef, sha: pull.baseSha, label: `${repo.owner}:${pull.baseRef}` },
    merged: pull.merged,
    merged_at: pull.mergedAt,
    merge_commit_sha: pull.mergeCommitSha,
    mergeable: mergeableState(repo, pull) === 'MERGEABLE',
    user: { login: VIEWER_LOGIN, id: VIEWER_ID, type: 'User' },
    created_at: FIXED_TS,
    updated_at: FIXED_TS,
  };
}

function commentJson(repo: Repo, issueNumber: number, comment: IssueComment): Record<string, unknown> {
  return {
    id: comment.id,
    node_id: commentGlobalId(repo, issueNumber, comment),
    body: comment.body,
    user: { login: VIEWER_LOGIN, id: VIEWER_ID, type: 'User' },
    created_at: FIXED_TS,
    updated_at: FIXED_TS,
  };
}

// ---------------------------------------------------------------------------
// REST v3 handlers
// ---------------------------------------------------------------------------

function handleCreateRepo(res: ServerResponse, body: Record<string, unknown>): void {
  const name = strField(body, 'name');
  if (name === '' || !/^[A-Za-z0-9][A-Za-z0-9._-]{0,99}$/.test(name)) {
    sendError(res, 422, 'name is invalid');
    return;
  }
  if (repos.has(repoKey(VIEWER_LOGIN, name))) {
    sendError(res, 422, 'name already exists on this account');
    return;
  }
  const repo = createRepo(name, strField(body, 'description'), body.private === true);
  sendJson(res, 201, repoJson(repo));
}

function handleListUserRepos(req: IncomingMessage, res: ServerResponse, query: URLSearchParams): void {
  const all = [...repos.values()]
    .filter((repo) => repo.owner === VIEWER_LOGIN)
    .sort((a, b) => a.id - b.id)
    .map((repo) => repoJson(repo));
  const { page, link } = paginate(req, '/api/v3/user/repos', query, all);
  sendJson(res, 200, page, link === null ? {} : { link });
}

function handleGetRepo(res: ServerResponse, repo: Repo): void {
  sendJson(res, 200, repoJson(repo));
}

function handlePatchRepo(res: ServerResponse, repo: Repo, body: Record<string, unknown>): void {
  if (typeof body.description === 'string') repo.description = body.description;
  if (typeof body.private === 'boolean') repo.private = body.private;
  sendJson(res, 200, repoJson(repo));
}

function handleListBranches(res: ServerResponse, repo: Repo): void {
  const branches: { name: string; commit: { sha: string } }[] = [];
  for (const [ref, sha] of [...repo.refs.entries()].sort()) {
    if (ref.startsWith('refs/heads/')) branches.push({ name: ref.slice('refs/heads/'.length), commit: { sha } });
  }
  sendJson(res, 200, branches);
}

function handleGetBranch(res: ServerResponse, repo: Repo, branch: string): void {
  const sha = repo.refs.get(`refs/heads/${branch}`);
  if (sha === undefined) {
    sendError(res, 404, 'Branch not found');
    return;
  }
  sendJson(res, 200, { name: branch, commit: { sha }, protected: false });
}

function handleListCommits(req: IncomingMessage, res: ServerResponse, repo: Repo, query: URLSearchParams): void {
  const ref = query.get('sha') ?? repo.defaultBranch;
  const tip = resolveRef(repo, ref);
  if (tip === null) {
    sendError(res, 404, 'No commit found for this ref');
    return;
  }
  const commits = listCommits(repo, tip).map(({ sha, commit }) => ({
    sha,
    commit: {
      message: commit.message,
      author: { name: VIEWER_NAME, email: VIEWER_EMAIL },
      committer: { name: VIEWER_NAME, email: VIEWER_EMAIL },
    },
    author: { login: VIEWER_LOGIN, id: VIEWER_ID, type: 'User' },
    committer: { login: VIEWER_LOGIN, id: VIEWER_ID, type: 'User' },
  }));
  const { page, link } = paginate(req, `/api/v3/repos/${repo.owner}/${repo.name}/commits`, query, commits);
  sendJson(res, 200, page, link === null ? {} : { link });
}

function handleCreateGitRef(res: ServerResponse, repo: Repo, body: Record<string, unknown>): void {
  const ref = strField(body, 'ref');
  const sha = strField(body, 'sha');
  if (!ref.startsWith('refs/heads/') || ref.length > 200) {
    sendError(res, 422, 'ref is invalid');
    return;
  }
  if (!isHex40(sha) || repo.objects.get(sha)?.type !== 'commit') {
    sendError(res, 422, 'sha is not a commit this repository holds');
    return;
  }
  if (repo.refs.has(ref)) {
    sendError(res, 422, 'Reference already exists');
    return;
  }
  repo.refs.set(ref, sha);
  sendJson(res, 201, { ref, object: { sha } });
}

function handleGetGitRef(res: ServerResponse, repo: Repo, branch: string): void {
  const sha = repo.refs.get(`refs/heads/${branch}`);
  if (sha === undefined) {
    sendError(res, 404, 'Reference does not exist');
    return;
  }
  sendJson(res, 200, { ref: `refs/heads/${branch}`, object: { sha } });
}

function lookupPathInTree(repo: Repo, treeOid: string, segments: string[]): { entry: TreeEntry; parentTree: string } | null {
  let current = treeOid;
  for (let i = 0; i < segments.length; i += 1) {
    const object = repo.objects.get(current);
    if (!object || object.type !== 'tree') return null;
    const entry = parseTree(object.data).find((candidate) => candidate.name === segments[i]);
    if (!entry) return null;
    if (i === segments.length - 1) return { entry, parentTree: current };
    if (entry.mode !== '40000') return null;
    current = entry.oid;
  }
  return null;
}

function handlePutContents(res: ServerResponse, repo: Repo, segments: string[], body: Record<string, unknown>): void {
  const message = strField(body, 'message') || 'Update';
  const contentB64 = strField(body, 'content');
  if (contentB64 === '') {
    sendError(res, 422, 'content is required');
    return;
  }
  let content: Buffer;
  try {
    content = Buffer.from(contentB64.replace(/[\r\n\t ]+/g, ''), 'base64');
  } catch {
    sendError(res, 400, 'content is not valid base64');
    return;
  }
  const branch = strField(body, 'branch') || repo.defaultBranch;
  const sha = strField(body, 'sha') || null;
  const refName = `refs/heads/${branch}`;
  let tip = repo.refs.get(refName);
  if (tip === undefined && repo.refs.size > 0) {
    const defaultTip = repo.refs.get(`refs/heads/${repo.defaultBranch}`);
    if (defaultTip === undefined) {
      sendError(res, 404, 'Branch not found');
      return;
    }
    tip = defaultTip;
  }
  const path = segments.join('/');
  let currentTree: string | null = null;
  let currentBlob: string | null = null;
  if (tip !== undefined) {
    currentTree = treeOfCommit(repo, tip);
    if (currentTree !== null) {
      const flat = flattenTree(repo, currentTree);
      currentBlob = flat.get(path)?.oid ?? null;
    }
  }
  const exists = currentBlob !== null;
  if (sha !== null) {
    if (!exists || sha.toLowerCase() !== currentBlob!.toLowerCase()) {
      sendError(res, 409, 'sha does not match the current blob');
      return;
    }
  } else if (exists) {
    sendError(res, 422, 'file already exists');
    return;
  }
  const blobOid = storeObject(repo, 'blob', content);
  const newTree = setPathInTree(repo, currentTree, segments, blobOid);
  const commitOid = createServerCommit(repo, newTree, tip === undefined ? [] : [tip], message);
  repo.refs.set(refName, commitOid);
  sendJson(res, exists ? 200 : 201, {
    content: { name: segments[segments.length - 1], path, sha: blobOid, size: content.length, encoding: 'base64' },
    commit: { sha: commitOid },
  });
}

function handleGetContents(req: IncomingMessage, res: ServerResponse, repo: Repo, segments: string[], query: URLSearchParams): void {
  const ref = query.get('ref') ?? repo.defaultBranch;
  const tip = resolveRef(repo, ref);
  if (tip === null) {
    sendError(res, 404, 'No commit found for this ref');
    return;
  }
  const treeOid = treeOfCommit(repo, tip);
  if (treeOid === null) {
    sendError(res, 404, 'Not Found');
    return;
  }
  const path = segments.join('/');
  if (segments.length === 0) {
    const object = repo.objects.get(treeOid);
    const entries = object?.type === 'tree' ? parseTree(object.data) : [];
    sendJson(res, 200, entries.map((entry) => ({
      type: entry.mode === '40000' ? 'dir' : 'file',
      name: entry.name,
      path: entry.name,
      sha: entry.oid,
      size: entry.mode === '40000' ? 0 : (repo.objects.get(entry.oid)?.data.length ?? 0),
    })));
    return;
  }
  const found = lookupPathInTree(repo, treeOid, segments);
  if (found === null) {
    sendError(res, 404, 'Not Found');
    return;
  }
  const { entry } = found;
  if (entry.mode === '40000') {
    const object = repo.objects.get(entry.oid);
    const children = object?.type === 'tree' ? parseTree(object.data) : [];
    sendJson(res, 200, children.map((child) => ({
      type: child.mode === '40000' ? 'dir' : 'file',
      name: child.name,
      path: `${path}/${child.name}`,
      sha: child.oid,
      size: child.mode === '40000' ? 0 : (repo.objects.get(child.oid)?.data.length ?? 0),
    })));
    return;
  }
  const blob = repo.objects.get(entry.oid);
  if (!blob || blob.type !== 'blob') {
    sendError(res, 404, 'Not Found');
    return;
  }
  sendJson(res, 200, {
    type: 'file',
    encoding: 'base64',
    size: blob.data.length,
    name: entry.name,
    path,
    sha: entry.oid,
    content: blob.data.toString('base64'),
  });
}

function handleDeleteContents(res: ServerResponse, repo: Repo, segments: string[], body: Record<string, unknown>): void {
  const message = strField(body, 'message') || 'Delete';
  const sha = strField(body, 'sha') || null;
  const branch = strField(body, 'branch') || repo.defaultBranch;
  const refName = `refs/heads/${branch}`;
  const tip = repo.refs.get(refName);
  if (tip === undefined) {
    sendError(res, 404, 'Branch not found');
    return;
  }
  const treeOid = treeOfCommit(repo, tip);
  if (treeOid === null) {
    sendError(res, 404, 'Not Found');
    return;
  }
  const path = segments.join('/');
  const flat = flattenTree(repo, treeOid);
  const currentBlob = flat.get(path)?.oid ?? null;
  if (currentBlob === null) {
    sendError(res, 404, 'Not Found');
    return;
  }
  if (sha !== null && sha.toLowerCase() !== currentBlob.toLowerCase()) {
    sendError(res, 409, 'sha does not match the current blob');
    return;
  }
  const newTree = setPathInTree(repo, treeOid, segments, null);
  const commitOid = createServerCommit(repo, newTree, [tip], message);
  repo.refs.set(refName, commitOid);
  sendJson(res, 200, { commit: { sha: commitOid }, content: null });
}

function handleCreateLabel(res: ServerResponse, repo: Repo, body: Record<string, unknown>): void {
  const name = strField(body, 'name');
  const color = strField(body, 'color') || 'ededed';
  if (name === '') {
    sendError(res, 422, 'name is required');
    return;
  }
  const existing = repo.labels.get(name);
  if (existing) {
    sendJson(res, 201, { name: existing.name, color: existing.color });
    return;
  }
  const label: Label = { name, color };
  repo.labels.set(name, label);
  sendJson(res, 201, { name, color });
}

function createIssueInRepo(repo: Repo, title: string, bodyText: string, labelNames: string[]): Issue | { error: string } {
  const labels: Label[] = [];
  for (const name of labelNames) {
    const label = repo.labels.get(name);
    if (!label) return { error: `Label does not exist: ${name}` };
    labels.push(label);
  }
  const issue: Issue = {
    id: nextIssueId++,
    number: repo.nextIssue++,
    title,
    body: bodyText,
    state: 'open',
    labels,
    seq: nextItemSeq++,
  };
  repo.issues.push(issue);
  return issue;
}

function handleCreateIssue(res: ServerResponse, repo: Repo, body: Record<string, unknown>): void {
  const title = strField(body, 'title');
  if (title === '') {
    sendError(res, 422, 'title is required');
    return;
  }
  const labelNames = Array.isArray(body.labels) ? body.labels.filter((v): v is string => typeof v === 'string') : [];
  const created = createIssueInRepo(repo, title, strField(body, 'body'), labelNames);
  if ('error' in created) {
    sendError(res, 422, created.error);
    return;
  }
  sendJson(res, 201, issueJson(repo, created));
}

function listIssuesFiltered(repo: Repo, query: URLSearchParams): Issue[] {
  const state = query.get('state');
  let list = [...repo.issues];
  if (state === 'closed') list = list.filter((issue) => issue.state === 'closed');
  else if (state === 'all') list = list;
  else list = list.filter((issue) => issue.state === 'open');
  const sort = query.get('sort') ?? 'created';
  const direction = query.get('direction') ?? 'desc';
  if (sort === 'created') {
    list.sort((a, b) => (direction === 'asc' ? a.seq - b.seq : b.seq - a.seq));
  }
  return list;
}

function handleListIssues(req: IncomingMessage, res: ServerResponse, repo: Repo, query: URLSearchParams): void {
  const list = listIssuesFiltered(repo, query).map((issue) => issueJson(repo, issue));
  const { page, link } = paginate(req, `/api/v3/repos/${repo.owner}/${repo.name}/issues`, query, list);
  sendJson(res, 200, page, link === null ? {} : { link });
}

function handleGetIssue(res: ServerResponse, repo: Repo, number: number): void {
  const issue = repo.issues.find((entry) => entry.number === number);
  if (!issue) {
    sendError(res, 404, 'Issue not found');
    return;
  }
  sendJson(res, 200, issueJson(repo, issue));
}

function handlePatchIssue(res: ServerResponse, repo: Repo, number: number, body: Record<string, unknown>): void {
  const issue = repo.issues.find((entry) => entry.number === number);
  if (!issue) {
    sendError(res, 404, 'Issue not found');
    return;
  }
  if (body.state === 'open' || body.state === 'closed') issue.state = body.state;
  if (typeof body.title === 'string') issue.title = body.title;
  if (typeof body.body === 'string') issue.body = body.body;
  sendJson(res, 200, issueJson(repo, issue));
}

function handleCreateComment(res: ServerResponse, repo: Repo, number: number, body: Record<string, unknown>): void {
  const issue = repo.issues.find((entry) => entry.number === number);
  if (!issue) {
    sendError(res, 404, 'Issue not found');
    return;
  }
  const text = strField(body, 'body');
  if (text === '') {
    sendError(res, 422, 'body is required');
    return;
  }
  const comment: IssueComment = { id: repo.nextComment++, body: text };
  const list = repo.comments.get(number) ?? [];
  list.push(comment);
  repo.comments.set(number, list);
  sendJson(res, 201, commentJson(repo, number, comment));
}

function handleListComments(res: ServerResponse, repo: Repo, number: number): void {
  const issue = repo.issues.find((entry) => entry.number === number);
  if (!issue) {
    sendError(res, 404, 'Issue not found');
    return;
  }
  sendJson(res, 200, (repo.comments.get(number) ?? []).map((comment) => commentJson(repo, number, comment)));
}

function createPullInRepo(repo: Repo, title: string, bodyText: string, head: string, base: string): Pull | { error: string; status: number } {
  const headTip = repo.refs.get(`refs/heads/${head}`);
  const baseTip = repo.refs.get(`refs/heads/${base}`);
  if (headTip === undefined || baseTip === undefined) return { error: 'head or base branch not found', status: 422 };
  const existing = repo.pulls.find((pull) => pull.headRef === head && pull.baseRef === base && pull.state === 'open');
  if (existing) return { error: 'a pull request already exists for this head branch', status: 422 };
  const pull: Pull = {
    id: nextPullId++,
    number: repo.nextPull++,
    title,
    body: bodyText,
    state: 'open',
    headRef: head,
    baseRef: base,
    headSha: headTip,
    baseSha: baseTip,
    merged: false,
    mergedAt: null,
    mergeCommitSha: null,
    seq: nextItemSeq++,
  };
  repo.pulls.push(pull);
  return pull;
}

function handleCreatePull(res: ServerResponse, repo: Repo, body: Record<string, unknown>): void {
  const title = strField(body, 'title');
  const head = strField(body, 'head');
  const base = strField(body, 'base');
  if (title === '' || head === '' || base === '') {
    sendError(res, 422, 'title, head and base are required');
    return;
  }
  const created = createPullInRepo(repo, title, strField(body, 'body'), head, base);
  if ('error' in created) {
    sendError(res, created.status, created.error);
    return;
  }
  sendJson(res, 201, pullJson(repo, created));
}

function listPullsFiltered(repo: Repo, query: URLSearchParams): Pull[] {
  const state = query.get('state');
  let list = [...repo.pulls];
  if (state === 'closed') list = list.filter((pull) => pull.state === 'closed');
  else if (state === 'all') list = list;
  else list = list.filter((pull) => pull.state === 'open');
  const direction = query.get('direction') ?? 'desc';
  list.sort((a, b) => (direction === 'asc' ? a.seq - b.seq : b.seq - a.seq));
  return list;
}

function handleListPulls(req: IncomingMessage, res: ServerResponse, repo: Repo, query: URLSearchParams): void {
  const list = listPullsFiltered(repo, query).map((pull) => pullJson(repo, pull));
  const { page, link } = paginate(req, `/api/v3/repos/${repo.owner}/${repo.name}/pulls`, query, list);
  sendJson(res, 200, page, link === null ? {} : { link });
}

function handleGetPull(res: ServerResponse, repo: Repo, number: number): void {
  const pull = repo.pulls.find((entry) => entry.number === number);
  if (!pull) {
    sendError(res, 404, 'Pull request not found');
    return;
  }
  sendJson(res, 200, pullJson(repo, pull));
}

function handleListPullFiles(res: ServerResponse, repo: Repo, number: number): void {
  const pull = repo.pulls.find((entry) => entry.number === number);
  if (!pull) {
    sendError(res, 404, 'Pull request not found');
    return;
  }
  const base = mergeBase(repo, pull.baseSha, pull.headSha) ?? pull.baseSha;
  const files = diffTrees(repo, treeOfCommit(repo, base), treeOfCommit(repo, pull.headSha)).map((change) => ({
    filename: change.path,
    status: change.status,
    additions: change.additions,
    deletions: change.deletions,
    changes: change.changes,
  }));
  sendJson(res, 200, files);
}

function mergePullInRepo(repo: Repo, pull: Pull): { sha: string } | { error: string; status: number } {
  if (pull.state !== 'open') return { error: 'pull request is not open', status: 405 };
  const baseTip = repo.refs.get(`refs/heads/${pull.baseRef}`);
  const headTip = repo.refs.get(`refs/heads/${pull.headRef}`);
  if (baseTip === undefined || headTip === undefined) return { error: 'head or base branch not found', status: 422 };
  if (mergeConflicts(repo, baseTip, headTip)) return { error: 'merge conflict', status: 405 };
  const headTree = treeOfCommit(repo, headTip);
  if (headTree === null) return { error: 'head commit not found', status: 422 };
  const mergeSha = createServerCommit(repo, headTree, [baseTip], pull.title);
  repo.refs.set(`refs/heads/${pull.baseRef}`, mergeSha);
  pull.state = 'closed';
  pull.merged = true;
  pull.mergedAt = FIXED_TS;
  pull.mergeCommitSha = mergeSha;
  return { sha: mergeSha };
}

function handleMergePull(res: ServerResponse, repo: Repo, number: number): void {
  const pull = repo.pulls.find((entry) => entry.number === number);
  if (!pull) {
    sendError(res, 404, 'Pull request not found');
    return;
  }
  const merged = mergePullInRepo(repo, pull);
  if ('error' in merged) {
    sendError(res, merged.status, merged.error);
    return;
  }
  sendJson(res, 200, { sha: merged.sha, merged: true, message: `Merged pull request #${pull.number}` });
}

// ---------------------------------------------------------------------------
// git smart HTTP
// ---------------------------------------------------------------------------

const V0_UPLOAD_CAPS = `symref=HEAD:refs/heads/${DEFAULT_BRANCH} side-band-64k ofs-delta thin-pack multi_ack multi_ack_detailed shallow`;
const V0_RECEIVE_CAPS = 'report-status side-band-64k delete-refs';
const SIDEBAND_MAX = 65515;

function sendRaw(res: ServerResponse, status: number, contentType: string, body: Buffer): void {
  res.writeHead(status, { 'content-type': contentType, 'content-length': body.length });
  res.end(body);
}

function sortedRefs(repo: Repo): { name: string; oid: string }[] {
  return [...repo.refs.entries()]
    .filter(([name]) => name.startsWith('refs/'))
    .sort(([a], [b]) => (a < b ? -1 : a > b ? 1 : 0))
    .map(([name, oid]) => ({ name, oid }));
}

function peeledOid(repo: Repo, oid: string): string | null {
  const object = repo.objects.get(oid);
  if (!object || object.type !== 'tag') return null;
  return parseTag(object.data).object;
}

function sidebandChunks(pack: Buffer): Buffer[] {
  const out: Buffer[] = [];
  let offset = 0;
  while (offset < pack.length) {
    const chunk = pack.subarray(offset, offset + SIDEBAND_MAX);
    out.push(encodePktLine(Buffer.concat([Buffer.from([1]), chunk])));
    offset += chunk.length;
  }
  return out;
}

function handleInfoRefs(req: IncomingMessage, res: ServerResponse, repo: Repo, service: string): void {
  const refs = sortedRefs(repo);
  const headTip = repo.refs.get(`refs/heads/${repo.defaultBranch}`) ?? refs[0]?.oid;
  if (service === 'git-upload-pack' && (req.headers['git-protocol'] ?? '').includes('version=2')) {
    sendRaw(res, 200, 'application/x-git-upload-pack-advertisement', Buffer.concat([
      encodePktLine('version 2\n'),
      encodePktLine('ls-refs=unborn\n'),
      encodePktLine('fetch=shallow filter\n'),
      encodePktLine('object-format=sha1\n'),
      PKT_FLUSH,
    ]));
    return;
  }
  const out: Buffer[] = [];
  if (service === 'git-upload-pack') {
    out.push(encodePktLine('# service=git-upload-pack\n'));
    out.push(PKT_FLUSH);
    if (refs.length === 0) {
      out.push(encodePktLine(`${ZERO_OID} capabilities^{}\0${V0_UPLOAD_CAPS}\n`));
    } else {
      out.push(encodePktLine(`${headTip} HEAD\0${V0_UPLOAD_CAPS}\n`));
      for (const { name, oid } of refs) {
        out.push(encodePktLine(`${oid} ${name}\n`));
        const peeled = peeledOid(repo, oid);
        if (peeled !== null) out.push(encodePktLine(`${peeled} ${name}^{}\n`));
      }
    }
    out.push(PKT_FLUSH);
    sendRaw(res, 200, 'application/x-git-upload-pack-advertisement', Buffer.concat(out));
    return;
  }
  out.push(encodePktLine('# service=git-receive-pack\n'));
  out.push(PKT_FLUSH);
  if (refs.length === 0) {
    out.push(encodePktLine(`${ZERO_OID} capabilities^{}\0${V0_RECEIVE_CAPS}\n`));
  } else {
    out.push(encodePktLine(`${headTip} HEAD\0${V0_RECEIVE_CAPS}\n`));
    for (const { name, oid } of refs) {
      out.push(encodePktLine(`${oid} ${name}\n`));
      const peeled = peeledOid(repo, oid);
      if (peeled !== null) out.push(encodePktLine(`${peeled} ${name}^{}\n`));
    }
  }
  out.push(PKT_FLUSH);
  sendRaw(res, 200, 'application/x-git-receive-pack-advertisement', Buffer.concat(out));
}

interface FetchResult {
  ack: string | null;
  shallow: string[];
  unshallow: string[];
  shallowInfo: boolean;
  pack: Buffer | null;
}

function addTreeClosureTo(set: Set<string>, repo: Repo, treeOid: string): void {
  const treeObject = repo.objects.get(treeOid);
  if (!treeObject || treeObject.type !== 'tree') return;
  if (set.has(treeOid)) return;
  set.add(treeOid);
  for (const entry of parseTree(treeObject.data)) {
    if (entry.mode === '40000') addTreeClosureTo(set, repo, entry.oid);
    else set.add(entry.oid);
  }
}

/**
 * Select the objects for a fetch: reachable(wants) minus what the client already holds.
 * A normal have means the client holds the commit and its whole history; a shallow-boundary
 * have contributes only itself + its tree + blobs. Depth N includes commits closer than N
 * from a want; an included commit whose parents were cut off is a new shallow boundary.
 */
function computeFetch(repo: Repo, wants: string[], haves: string[], clientShallows: string[], deepen: number | null, filterBlobNone: boolean): FetchResult {
  const wantCommits: string[] = [];
  const tagObjects = new Set<string>();
  for (const want of wants) {
    const object = repo.objects.get(want);
    if (!object) continue;
    if (object.type === 'commit') wantCommits.push(want);
    else if (object.type === 'tag') {
      tagObjects.add(want);
      const target = peelToCommit(repo, want);
      if (target !== null) wantCommits.push(target);
    }
  }
  const haveSet = new Set(haves);
  const shallowSet = new Set(clientShallows);
  let ack: string | null = null;
  for (const have of haves) {
    const haveCommit = peelToCommit(repo, have);
    if (haveCommit === null) continue;
    for (const want of wantCommits) {
      if (isAncestor(repo, haveCommit, want)) {
        ack = have;
        break;
      }
    }
    if (ack !== null) break;
  }
  // What the client already holds: full history for a normal have, only the commit
  // itself + its tree + blobs for a shallow boundary.
  const heldObjects = new Set<string>();
  const addHeldCommit = (commitOid: string, includeAncestors: boolean): void => {
    const queue: string[] = [commitOid];
    const seen = new Set<string>();
    while (queue.length) {
      const oid = queue.pop()!;
      if (seen.has(oid)) continue;
      seen.add(oid);
      const object = repo.objects.get(oid);
      if (!object) continue;
      if (object.type === 'commit') {
        heldObjects.add(oid);
        addTreeClosureTo(heldObjects, repo, parseCommit(object.data).tree);
        if (includeAncestors) {
          for (const parent of parseCommit(object.data).parents) queue.push(parent);
        }
      } else if (object.type === 'tag') {
        heldObjects.add(oid);
        const target = parseTag(object.data).object;
        const targetObject = repo.objects.get(target);
        if (targetObject?.type === 'commit') queue.push(target);
        else if (targetObject) heldObjects.add(target);
      } else {
        heldObjects.add(oid);
      }
    }
  };
  for (const have of haves) {
    const haveCommit = peelToCommit(repo, have);
    if (haveCommit === null) continue;
    addHeldCommit(haveCommit, !shallowSet.has(have));
  }
  for (const boundary of clientShallows) {
    if (haveSet.has(boundary)) continue;
    const boundaryCommit = peelToCommit(repo, boundary);
    if (boundaryCommit === null) continue;
    addHeldCommit(boundaryCommit, false);
  }
  const included = new Set<string>();
  const queue: { oid: string; depth: number }[] = wantCommits.map((oid) => ({ oid, depth: 0 }));
  const visited = new Set<string>();
  while (queue.length) {
    const { oid, depth } = queue.shift()!;
    if (visited.has(oid)) continue;
    visited.add(oid);
    if (haveSet.has(oid) || shallowSet.has(oid)) {
      // Held by the client: not re-sent, but the search continues past it so a
      // deepen or an incremental fetch can reach the new ancestors.
      const object = repo.objects.get(oid);
      if (object?.type === 'commit') {
        for (const parent of parseCommit(object.data).parents) queue.push({ oid: parent, depth: depth + 1 });
      }
      continue;
    }
    if (deepen !== null && depth >= deepen) continue;
    included.add(oid);
    const object = repo.objects.get(oid);
    if (object?.type === 'commit') {
      for (const parent of parseCommit(object.data).parents) queue.push({ oid: parent, depth: depth + 1 });
    }
  }
  // An included commit whose parents were cut off is a new shallow boundary.
  const newShallow = new Set<string>();
  for (const oid of included) {
    const object = repo.objects.get(oid);
    if (!object || object.type !== 'commit') continue;
    const parents = parseCommit(object.data).parents;
    if (parents.length > 0 && parents.some((parent) => !included.has(parent))) newShallow.add(oid);
  }
  // A former boundary whose parents are all in the pack is no longer shallow.
  const unshallow = [...clientShallows].filter((oid) => {
    const commit = peelToCommit(repo, oid);
    if (commit === null) return false;
    const object = repo.objects.get(commit);
    if (!object || object.type !== 'commit') return false;
    const parents = parseCommit(object.data).parents;
    return parents.length > 0 && parents.every((parent) => included.has(parent));
  }).sort();
  const objects = new Map<string, GitObject>();
  const addObject = (oid: string): void => {
    if (heldObjects.has(oid)) return;
    const object = repo.objects.get(oid);
    if (object && !objects.has(oid)) objects.set(oid, object);
  };
  const addTreeClosure = (treeOid: string): void => {
    const treeObject = repo.objects.get(treeOid);
    if (!treeObject || treeObject.type !== 'tree') return;
    addObject(treeOid);
    for (const entry of parseTree(treeObject.data)) {
      if (entry.mode === '40000') addTreeClosure(entry.oid);
      else addObject(entry.oid);
    }
  };
  for (const tagOid of tagObjects) addObject(tagOid);
  for (const commitOid of included) {
    addObject(commitOid);
    const treeOid = treeOfCommit(repo, commitOid);
    if (treeOid !== null) addTreeClosure(treeOid);
  }
  if (filterBlobNone) {
    for (const [oid, object] of [...objects.entries()]) {
      if (object.type === 'blob') objects.delete(oid);
    }
  }
  const pack = objects.size === 0 ? null : writePack([...objects.entries()].map(([oid, object]) => ({ oid, ...object })));
  return { ack, shallow: [...newShallow].sort(), unshallow, shallowInfo: deepen !== null || clientShallows.length > 0, pack };
}

function handleUploadPackV2(res: ServerResponse, repo: Repo, body: Buffer): void {
  let parsed: { packets: PktItem[] };
  try {
    parsed = parsePktLines(body);
  } catch {
    sendError(res, 400, 'malformed git request');
    return;
  }
  const lines = pktLinesText(parsed.packets);
  const command = lines[0]?.trim() ?? '';
  if (command === 'command=ls-refs') {
    let prefix: string | null = null;
    for (const line of lines.slice(1)) {
      const trimmed = line.trim();
      if (trimmed.startsWith('ref-prefix ')) prefix = trimmed.slice('ref-prefix '.length).trim();
    }
    const out: Buffer[] = [];
    const refs = sortedRefs(repo);
    const headTip = repo.refs.get(`refs/heads/${repo.defaultBranch}`);
    const includeHead = prefix === null || 'HEAD'.startsWith(prefix);
    if (refs.length === 0) {
      out.push(encodePktLine(`unborn HEAD symref-target:refs/heads/${repo.defaultBranch}\n`));
    } else {
      if (includeHead && headTip !== undefined) {
        out.push(encodePktLine(`${headTip} HEAD symref-target:refs/heads/${repo.defaultBranch}\n`));
      }
      for (const { name, oid } of refs) {
        if (prefix !== null && !name.startsWith(prefix)) continue;
        const peeled = peeledOid(repo, oid);
        out.push(encodePktLine(peeled !== null ? `${oid} ${name} peeled:${peeled}\n` : `${oid} ${name}\n`));
      }
    }
    out.push(PKT_FLUSH);
    sendRaw(res, 200, 'application/x-git-upload-pack-result', Buffer.concat(out));
    return;
  }
  if (command === 'command=fetch') {
    const wants: string[] = [];
    const haves: string[] = [];
    const shallows: string[] = [];
    let deepen: number | null = null;
    let filterBlobNone = false;
    for (const line of lines.slice(1)) {
      const trimmed = line.trim();
      if (trimmed.startsWith('want ')) wants.push(trimmed.slice(5).trim().split(/\s+/)[0] ?? '');
      else if (trimmed.startsWith('have ')) haves.push(trimmed.slice(5).trim().split(/\s+/)[0] ?? '');
      else if (trimmed.startsWith('shallow ')) shallows.push(trimmed.slice(8).trim().split(/\s+/)[0] ?? '');
      else if (trimmed.startsWith('deepen ')) deepen = Number.parseInt(trimmed.slice(7).trim(), 10);
      else if (trimmed.startsWith('filter ') && trimmed.includes('blob:none')) filterBlobNone = true;
    }
    const result = computeFetch(repo, wants, haves, shallows, deepen, filterBlobNone);
    const out: Buffer[] = [];
    out.push(encodePktLine('acknowledgments\n'));
    out.push(encodePktLine(result.ack !== null ? `ACK ${result.ack}\n` : 'NAK\n'));
    out.push(PKT_FLUSH);
    if (result.shallowInfo) {
      out.push(encodePktLine('shallow-info\n'));
      for (const oid of result.shallow) out.push(encodePktLine(`shallow ${oid}\n`));
      for (const oid of result.unshallow) out.push(encodePktLine(`unshallow ${oid}\n`));
      out.push(PKT_FLUSH);
    }
    if (result.pack !== null) {
      out.push(encodePktLine('packfile\n'));
      out.push(...sidebandChunks(result.pack));
    }
    sendRaw(res, 200, 'application/x-git-upload-pack-result', Buffer.concat(out));
    return;
  }
  sendError(res, 400, 'unknown git command');
}

function handleUploadPackV0(res: ServerResponse, repo: Repo, body: Buffer): void {
  let parsed: { packets: PktItem[] };
  try {
    parsed = parsePktLines(body);
  } catch {
    sendError(res, 400, 'malformed git request');
    return;
  }
  const wants: string[] = [];
  const haves: string[] = [];
  const shallows: string[] = [];
  let deepen: number | null = null;
  let filterBlobNone = false;
  for (const packet of parsed.packets) {
    if (packet.kind !== 'data') continue;
    const text = packet.payload.toString('utf8');
    const nul = text.indexOf('\0');
    const line = (nul >= 0 ? text.slice(0, nul) : text).trim();
    if (line.startsWith('want ')) wants.push(line.slice(5).trim().split(/\s+/)[0] ?? '');
    else if (line.startsWith('have ')) haves.push(line.slice(5).trim().split(/\s+/)[0] ?? '');
    else if (line.startsWith('shallow ')) shallows.push(line.slice(8).trim().split(/\s+/)[0] ?? '');
    else if (line.startsWith('deepen ')) deepen = Number.parseInt(line.slice(7).trim(), 10);
    else if (line.startsWith('filter ') && line.includes('blob:none')) filterBlobNone = true;
  }
  if (wants.length === 0) {
    sendError(res, 400, 'no want lines');
    return;
  }
  const result = computeFetch(repo, wants, haves, shallows, deepen, filterBlobNone);
  const out: Buffer[] = [];
  out.push(encodePktLine(result.ack !== null ? `ACK ${result.ack}\n` : 'NAK\n'));
  for (const oid of result.shallow) out.push(encodePktLine(`shallow ${oid}\n`));
  for (const oid of result.unshallow) out.push(encodePktLine(`unshallow ${oid}\n`));
  if (result.pack !== null) {
    out.push(...sidebandChunks(result.pack));
    out.push(PKT_FLUSH);
  }
  sendRaw(res, 200, 'application/x-git-upload-pack-result', Buffer.concat(out));
}

async function handleUploadPack(req: IncomingMessage, res: ServerResponse, repo: Repo): Promise<void> {
  const body = await readBody(req);
  if ((req.headers['git-protocol'] ?? '').includes('version=2')) handleUploadPackV2(res, repo, body);
  else handleUploadPackV0(res, repo, body);
}

function applyRefUpdate(repo: Repo, oldOid: string, newOid: string, ref: string): string {
  if (!ref.startsWith('refs/')) return `ng ${ref} invalid ref`;
  const current = repo.refs.get(ref);
  if (newOid === ZERO_OID) {
    if (current === undefined) return `ng ${ref} reference does not exist`;
    if (oldOid !== ZERO_OID && oldOid !== current) return `ng ${ref} non-fast-forward`;
    repo.refs.delete(ref);
    return `ok ${ref}`;
  }
  if (repo.objects.get(newOid) === undefined) return `ng ${ref} object not found`;
  if (oldOid === ZERO_OID) {
    if (current !== undefined) return `ng ${ref} reference already exists`;
    repo.refs.set(ref, newOid);
    return `ok ${ref}`;
  }
  if (oldOid === newOid) return `ok ${ref}`;
  if (current === undefined) return `ng ${ref} reference does not exist`;
  if (current !== oldOid) return `ng ${ref} non-fast-forward`;
  const oldCommit = peelToCommit(repo, oldOid);
  const newCommit = peelToCommit(repo, newOid);
  if (oldCommit === null || newCommit === null) return `ng ${ref} non-fast-forward`;
  if (!isAncestor(repo, oldCommit, newCommit)) return `ng ${ref} non-fast-forward`;
  repo.refs.set(ref, newOid);
  return `ok ${ref}`;
}

async function handleReceivePack(req: IncomingMessage, res: ServerResponse, repo: Repo): Promise<void> {
  const body = await readBody(req);
  let parsed: { packets: PktItem[]; next: number };
  try {
    parsed = parsePktLines(body);
  } catch {
    sendError(res, 400, 'malformed git request');
    return;
  }
  const commands: { oldOid: string; newOid: string; ref: string }[] = [];
  let index = 0;
  for (; index < parsed.packets.length; index += 1) {
    const packet = parsed.packets[index]!;
    if (packet.kind === 'flush' || packet.kind === 'delim') {
      index += 1;
      break;
    }
    if (packet.kind !== 'data') continue;
    const text = packet.payload.toString('utf8');
    const nul = text.indexOf('\0');
    const line = (nul >= 0 ? text.slice(0, nul) : text).trim();
    const parts = line.split(' ');
    if (parts.length !== 3 || !isHex40(parts[0]!) || !isHex40(parts[1]!)) {
      sendError(res, 400, 'malformed ref update line');
      return;
    }
    commands.push({ oldOid: parts[0]!, newOid: parts[1]!, ref: parts[2]! });
  }
  if (commands.length === 0) {
    sendError(res, 400, 'no ref updates');
    return;
  }
  const packBytes = body.subarray(parsed.next);
  // A delete-only command list carries no pack at all; any create/update needs one.
  const hasUpdates = commands.some((command) => command.newOid !== ZERO_OID);
  if (packBytes.length === 0 && hasUpdates) {
    sendError(res, 400, 'missing packfile');
    return;
  }
  let pack: Map<string, GitObject> = new Map();
  if (packBytes.length > 0) {
    try {
      pack = readPack(packBytes);
    } catch {
      sendError(res, 400, 'malformed packfile');
      return;
    }
  }
  for (const [oid, object] of pack) {
    if (!repo.objects.has(oid)) {
      repo.objects.set(oid, object);
      if (object.type === 'commit' && !repo.commitSeq.has(oid)) repo.commitSeq.set(oid, nextCommitSeq++);
    }
  }
  const out: Buffer[] = [];
  out.push(encodePktLine(Buffer.concat([Buffer.from([1]), Buffer.from('unpack ok\n', 'utf8')])));
  for (const { oldOid, newOid, ref } of commands) {
    const line = applyRefUpdate(repo, oldOid, newOid, ref);
    out.push(encodePktLine(Buffer.concat([Buffer.from([1]), Buffer.from(`${line}\n`, 'utf8')])));
  }
  out.push(PKT_FLUSH);
  sendRaw(res, 200, 'application/x-git-receive-pack-result', Buffer.concat(out));
}

// ---------------------------------------------------------------------------
// GraphQL: schema tables
// ---------------------------------------------------------------------------

interface FieldDesc {
  name: string;
  type: string;
  args?: { name: string; type: string; defaultValue?: unknown }[];
  deprecated?: boolean;
}

interface TypeDesc {
  kind: 'OBJECT' | 'ENUM' | 'INPUT_OBJECT' | 'SCALAR' | 'INTERFACE';
  name: string;
  fields?: FieldDesc[];
  enumValues?: { name: string; deprecated?: boolean }[];
  inputFields?: { name: string; type: string }[];
}

const SCHEMA: Record<string, TypeDesc> = {
  Query: {
    kind: 'OBJECT', name: 'Query', fields: [
      { name: 'viewer', type: 'User' },
      { name: 'repository', type: 'Repository', args: [{ name: 'owner', type: 'String!' }, { name: 'name', type: 'String!' }] },
      { name: 'node', type: 'Node', args: [{ name: 'id', type: 'ID!' }] },
      { name: 'search', type: 'SearchResultItemConnection', args: [{ name: 'type', type: 'SearchType!' }, { name: 'query', type: 'String!' }, { name: 'first', type: 'Int' }] },
      { name: '__type', type: '__Type', args: [{ name: 'name', type: 'String!' }] },
      { name: '__schema', type: '__Schema' },
    ],
  },
  Mutation: {
    kind: 'OBJECT', name: 'Mutation', fields: [
      { name: 'createIssue', type: 'CreateIssuePayload', args: [{ name: 'input', type: 'CreateIssueInput!' }] },
      { name: 'closeIssue', type: 'CloseIssuePayload', args: [{ name: 'input', type: 'CloseIssueInput!' }] },
      { name: 'createPullRequest', type: 'CreatePullRequestPayload', args: [{ name: 'input', type: 'CreatePullRequestInput!' }] },
      { name: 'mergePullRequest', type: 'MergePullRequestPayload', args: [{ name: 'input', type: 'MergePullRequestInput!' }] },
      { name: 'addComment', type: 'AddCommentPayload', args: [{ name: 'input', type: 'AddCommentInput!' }] },
    ],
  },
  User: {
    kind: 'OBJECT', name: 'User', fields: [
      { name: 'login', type: 'String' }, { name: 'id', type: 'ID' }, { name: 'name', type: 'String' },
      { name: 'email', type: 'String' }, { name: 'url', type: 'String' },
    ],
  },
  Repository: {
    kind: 'OBJECT', name: 'Repository', fields: [
      { name: 'id', type: 'ID' }, { name: 'databaseId', type: 'Int' }, { name: 'name', type: 'String' },
      { name: 'nameWithOwner', type: 'String' }, { name: 'owner', type: 'User' },
      { name: 'description', type: 'String' }, { name: 'url', type: 'String' },
      { name: 'defaultBranchRef', type: 'Ref' }, { name: 'viewerPermission', type: 'String' },
      { name: 'hasIssuesEnabled', type: 'Boolean' }, { name: 'createdAt', type: 'String' }, { name: 'updatedAt', type: 'String' },
      { name: 'issue', type: 'Issue', args: [{ name: 'number', type: 'Int!' }] },
      { name: 'issues', type: 'IssueConnection', args: [{ name: 'first', type: 'Int' }, { name: 'after', type: 'String' }, { name: 'states', type: '[IssueState!]' }, { name: 'orderBy', type: 'IssueOrder' }] },
      { name: 'pullRequest', type: 'PullRequest', args: [{ name: 'number', type: 'Int!' }] },
      { name: 'pullRequests', type: 'PullRequestConnection', args: [{ name: 'first', type: 'Int' }, { name: 'after', type: 'String' }, { name: 'states', type: '[PullRequestState!]' }, { name: 'orderBy', type: 'PullRequestOrder' }] },
    ],
  },
  Issue: {
    kind: 'OBJECT', name: 'Issue', fields: [
      { name: 'id', type: 'ID' }, { name: 'databaseId', type: 'Int' }, { name: 'number', type: 'Int' },
      { name: 'title', type: 'String' }, { name: 'body', type: 'String' }, { name: 'state', type: 'IssueState' },
      { name: 'url', type: 'String' }, { name: 'author', type: 'User' }, { name: 'repository', type: 'Repository' },
      { name: 'createdAt', type: 'String' }, { name: 'updatedAt', type: 'String' },
      { name: 'comments', type: 'IssueCommentConnection', args: [{ name: 'first', type: 'Int' }, { name: 'after', type: 'String' }] },
    ],
  },
  PullRequest: {
    kind: 'OBJECT', name: 'PullRequest', fields: [
      { name: 'id', type: 'ID' }, { name: 'databaseId', type: 'Int' }, { name: 'number', type: 'Int' },
      { name: 'title', type: 'String' }, { name: 'body', type: 'String' }, { name: 'state', type: 'PullRequestState' },
      { name: 'merged', type: 'Boolean' }, { name: 'mergeable', type: 'MergeableState' },
      { name: 'headRefName', type: 'String' }, { name: 'baseRefName', type: 'String' },
      { name: 'headRefOid', type: 'String' }, { name: 'baseRefOid', type: 'String' },
      { name: 'url', type: 'String' }, { name: 'author', type: 'User' }, { name: 'repository', type: 'Repository' },
      { name: 'createdAt', type: 'String' }, { name: 'updatedAt', type: 'String' },
      { name: 'files', type: 'PullRequestFileConnection', args: [{ name: 'first', type: 'Int' }, { name: 'after', type: 'String' }] },
    ],
  },
  IssueComment: {
    kind: 'OBJECT', name: 'IssueComment', fields: [
      { name: 'id', type: 'ID' }, { name: 'databaseId', type: 'Int' }, { name: 'body', type: 'String' },
      { name: 'author', type: 'User' }, { name: 'createdAt', type: 'String' }, { name: 'updatedAt', type: 'String' },
    ],
  },
  Ref: {
    kind: 'OBJECT', name: 'Ref', fields: [
      { name: 'name', type: 'String' }, { name: 'target', type: 'GitObject' },
    ],
  },
  GitObject: {
    kind: 'OBJECT', name: 'GitObject', fields: [
      { name: 'oid', type: 'String' }, { name: 'type', type: 'String' },
    ],
  },
  IssueConnection: {
    kind: 'OBJECT', name: 'IssueConnection', fields: [
      { name: 'nodes', type: '[Issue]' }, { name: 'edges', type: '[IssueEdge]' },
      { name: 'pageInfo', type: 'PageInfo' }, { name: 'totalCount', type: 'Int' },
    ],
  },
  IssueEdge: {
    kind: 'OBJECT', name: 'IssueEdge', fields: [
      { name: 'node', type: 'Issue' }, { name: 'cursor', type: 'String' },
    ],
  },
  PullRequestConnection: {
    kind: 'OBJECT', name: 'PullRequestConnection', fields: [
      { name: 'nodes', type: '[PullRequest]' }, { name: 'edges', type: '[PullRequestEdge]' },
      { name: 'pageInfo', type: 'PageInfo' }, { name: 'totalCount', type: 'Int' },
    ],
  },
  PullRequestEdge: {
    kind: 'OBJECT', name: 'PullRequestEdge', fields: [
      { name: 'node', type: 'PullRequest' }, { name: 'cursor', type: 'String' },
    ],
  },
  IssueCommentConnection: {
    kind: 'OBJECT', name: 'IssueCommentConnection', fields: [
      { name: 'nodes', type: '[IssueComment]' }, { name: 'edges', type: '[IssueCommentEdge]' },
      { name: 'pageInfo', type: 'PageInfo' }, { name: 'totalCount', type: 'Int' },
    ],
  },
  IssueCommentEdge: {
    kind: 'OBJECT', name: 'IssueCommentEdge', fields: [
      { name: 'node', type: 'IssueComment' }, { name: 'cursor', type: 'String' },
    ],
  },
  PullRequestFileConnection: {
    kind: 'OBJECT', name: 'PullRequestFileConnection', fields: [
      { name: 'nodes', type: '[PullRequestFile]' }, { name: 'edges', type: '[PullRequestFileEdge]' },
      { name: 'pageInfo', type: 'PageInfo' }, { name: 'totalCount', type: 'Int' },
    ],
  },
  PullRequestFileEdge: {
    kind: 'OBJECT', name: 'PullRequestFileEdge', fields: [
      { name: 'node', type: 'PullRequestFile' }, { name: 'cursor', type: 'String' },
    ],
  },
  PullRequestFile: {
    kind: 'OBJECT', name: 'PullRequestFile', fields: [
      { name: 'path', type: 'String' }, { name: 'filename', type: 'String' },
      { name: 'additions', type: 'Int' }, { name: 'deletions', type: 'Int' }, { name: 'changes', type: 'Int' },
      { name: 'changeType', type: 'String' }, { name: 'status', type: 'String' },
    ],
  },
  PageInfo: {
    kind: 'OBJECT', name: 'PageInfo', fields: [
      { name: 'hasNextPage', type: 'Boolean' }, { name: 'hasPreviousPage', type: 'Boolean' },
      { name: 'startCursor', type: 'String' }, { name: 'endCursor', type: 'String' },
    ],
  },
  SearchResultItemConnection: {
    kind: 'OBJECT', name: 'SearchResultItemConnection', fields: [
      { name: 'nodes', type: '[SearchResultItem]' }, { name: 'edges', type: '[SearchResultItemEdge]' },
      { name: 'pageInfo', type: 'PageInfo' }, { name: 'totalCount', type: 'Int' },
    ],
  },
  SearchResultItemEdge: {
    kind: 'OBJECT', name: 'SearchResultItemEdge', fields: [
      { name: 'node', type: 'SearchResultItem' }, { name: 'cursor', type: 'String' },
    ],
  },
  SearchResultItem: { kind: 'OBJECT', name: 'SearchResultItem', fields: [] },
  Node: { kind: 'INTERFACE', name: 'Node', fields: [{ name: 'id', type: 'ID' }] },
  CreateIssuePayload: {
    kind: 'OBJECT', name: 'CreateIssuePayload', fields: [
      { name: 'issue', type: 'Issue' }, { name: 'clientMutationId', type: 'String' },
    ],
  },
  CloseIssuePayload: {
    kind: 'OBJECT', name: 'CloseIssuePayload', fields: [
      { name: 'issue', type: 'Issue' }, { name: 'clientMutationId', type: 'String' },
    ],
  },
  CreatePullRequestPayload: {
    kind: 'OBJECT', name: 'CreatePullRequestPayload', fields: [
      { name: 'pullRequest', type: 'PullRequest' }, { name: 'clientMutationId', type: 'String' },
    ],
  },
  MergePullRequestPayload: {
    kind: 'OBJECT', name: 'MergePullRequestPayload', fields: [
      { name: 'pullRequest', type: 'PullRequest' }, { name: 'clientMutationId', type: 'String' },
    ],
  },
  AddCommentPayload: {
    kind: 'OBJECT', name: 'AddCommentPayload', fields: [
      { name: 'commentEdge', type: 'IssueCommentEdge' }, { name: 'comment', type: 'IssueComment' },
      { name: 'subject', type: 'Issue' }, { name: 'clientMutationId', type: 'String' },
    ],
  },
  IssueState: { kind: 'ENUM', name: 'IssueState', enumValues: [{ name: 'OPEN' }, { name: 'CLOSED' }] },
  PullRequestState: { kind: 'ENUM', name: 'PullRequestState', enumValues: [{ name: 'OPEN' }, { name: 'CLOSED' }, { name: 'MERGED' }] },
  MergeableState: { kind: 'ENUM', name: 'MergeableState', enumValues: [{ name: 'MERGEABLE' }, { name: 'CONFLICTING' }, { name: 'UNKNOWN' }] },
  SearchType: { kind: 'ENUM', name: 'SearchType', enumValues: [{ name: 'ISSUE' }, { name: 'REPOSITORY' }, { name: 'USER' }] },
  OrderDirection: { kind: 'ENUM', name: 'OrderDirection', enumValues: [{ name: 'ASC' }, { name: 'DESC' }] },
  IssueOrderField: { kind: 'ENUM', name: 'IssueOrderField', enumValues: [{ name: 'CREATED_AT' }, { name: 'UPDATED_AT' }, { name: 'COMMENTS' }] },
  PullRequestOrderField: { kind: 'ENUM', name: 'PullRequestOrderField', enumValues: [{ name: 'CREATED_AT' }, { name: 'UPDATED_AT' }] },
  IssueOrder: {
    kind: 'INPUT_OBJECT', name: 'IssueOrder', inputFields: [
      { name: 'field', type: 'IssueOrderField' }, { name: 'direction', type: 'OrderDirection' },
    ],
  },
  PullRequestOrder: {
    kind: 'INPUT_OBJECT', name: 'PullRequestOrder', inputFields: [
      { name: 'field', type: 'PullRequestOrderField' }, { name: 'direction', type: 'OrderDirection' },
    ],
  },
  CreateIssueInput: {
    kind: 'INPUT_OBJECT', name: 'CreateIssueInput', inputFields: [
      { name: 'repositoryId', type: 'ID!' }, { name: 'title', type: 'String!' },
      { name: 'body', type: 'String' }, { name: 'clientMutationId', type: 'String' },
    ],
  },
  CloseIssueInput: {
    kind: 'INPUT_OBJECT', name: 'CloseIssueInput', inputFields: [
      { name: 'issueId', type: 'ID!' }, { name: 'clientMutationId', type: 'String' },
    ],
  },
  CreatePullRequestInput: {
    kind: 'INPUT_OBJECT', name: 'CreatePullRequestInput', inputFields: [
      { name: 'repositoryId', type: 'ID!' }, { name: 'baseRefName', type: 'String!' },
      { name: 'headRefName', type: 'String!' }, { name: 'title', type: 'String!' },
      { name: 'body', type: 'String' }, { name: 'clientMutationId', type: 'String' },
    ],
  },
  MergePullRequestInput: {
    kind: 'INPUT_OBJECT', name: 'MergePullRequestInput', inputFields: [
      { name: 'pullRequestId', type: 'ID!' }, { name: 'mergeMethod', type: 'String' },
      { name: 'clientMutationId', type: 'String' },
    ],
  },
  AddCommentInput: {
    kind: 'INPUT_OBJECT', name: 'AddCommentInput', inputFields: [
      { name: 'subjectId', type: 'ID!' }, { name: 'body', type: 'String!' },
      { name: 'clientMutationId', type: 'String' },
    ],
  },
  __Schema: {
    kind: 'OBJECT', name: '__Schema', fields: [
      { name: 'types', type: '[__Type!]' }, { name: 'queryType', type: '__Type' },
      { name: 'mutationType', type: '__Type' }, { name: 'subscriptionType', type: '__Type' },
      { name: 'directives', type: '[__Directive!]' }, { name: 'description', type: 'String' },
    ],
  },
  __Type: {
    kind: 'OBJECT', name: '__Type', fields: [
      { name: 'name', type: 'String' }, { name: 'kind', type: '__TypeKind' },
      { name: 'description', type: 'String' },
      { name: 'fields', type: '[__Field!]', args: [{ name: 'includeDeprecated', type: 'Boolean', defaultValue: false }] },
      { name: 'enumValues', type: '[__EnumValue!]', args: [{ name: 'includeDeprecated', type: 'Boolean', defaultValue: false }] },
      { name: 'inputFields', type: '[__InputValue!]' },
      { name: 'interfaces', type: '[__Type!]' }, { name: 'possibleTypes', type: '[__Type!]' },
      { name: 'ofType', type: '__Type' }, { name: 'specifiedByURL', type: 'String' },
    ],
  },
  __Field: {
    kind: 'OBJECT', name: '__Field', fields: [
      { name: 'name', type: 'String' }, { name: 'description', type: 'String' },
      { name: 'args', type: '[__InputValue!]' }, { name: 'type', type: '__Type' },
      { name: 'isDeprecated', type: 'Boolean' }, { name: 'deprecationReason', type: 'String' },
    ],
  },
  __InputValue: {
    kind: 'OBJECT', name: '__InputValue', fields: [
      { name: 'name', type: 'String' }, { name: 'description', type: 'String' },
      { name: 'type', type: '__Type' }, { name: 'defaultValue', type: 'String' },
    ],
  },
  __EnumValue: {
    kind: 'OBJECT', name: '__EnumValue', fields: [
      { name: 'name', type: 'String' }, { name: 'description', type: 'String' },
      { name: 'isDeprecated', type: 'Boolean' }, { name: 'deprecationReason', type: 'String' },
    ],
  },
  __TypeKind: {
    kind: 'ENUM', name: '__TypeKind', enumValues: [
      { name: 'SCALAR' }, { name: 'OBJECT' }, { name: 'INTERFACE' }, { name: 'UNION' },
      { name: 'ENUM' }, { name: 'INPUT_OBJECT' }, { name: 'LIST' }, { name: 'NON_NULL' },
    ],
  },
  __Directive: { kind: 'OBJECT', name: '__Directive', fields: [{ name: 'name', type: 'String' }] },
  String: { kind: 'SCALAR', name: 'String' },
  Int: { kind: 'SCALAR', name: 'Int' },
  Float: { kind: 'SCALAR', name: 'Float' },
  Boolean: { kind: 'SCALAR', name: 'Boolean' },
  ID: { kind: 'SCALAR', name: 'ID' },
};

function schemaHasField(typeName: string, fieldName: string): boolean {
  const desc = SCHEMA[typeName];
  if (!desc || !desc.fields) return false;
  return desc.fields.some((field) => field.name === fieldName);
}

// ---------------------------------------------------------------------------
// GraphQL: parser
// ---------------------------------------------------------------------------

type GqlValue =
  | { kind: 'variable'; name: string }
  | { kind: 'string'; value: string }
  | { kind: 'int'; value: number }
  | { kind: 'boolean'; value: boolean }
  | { kind: 'enum'; value: string }
  | { kind: 'null' }
  | { kind: 'list'; values: GqlValue[] }
  | { kind: 'object'; fields: { name: string; value: GqlValue }[] };

interface GqlSelection {
  kind: 'field' | 'fragmentSpread' | 'inlineFragment';
  name?: string;
  alias?: string;
  args?: { name: string; value: GqlValue }[];
  selections?: GqlSelection[];
  typeCondition?: string;
}

interface GqlOperation {
  kind: 'query' | 'mutation';
  name?: string;
  variableDefinitions?: { name: string; type: string; defaultValue?: GqlValue }[];
  selections: GqlSelection[];
}

interface GqlDocument {
  operations: GqlOperation[];
  fragments: Map<string, GqlSelection[]>;
}

type GqlToken =
  | { type: 'punct'; value: string }
  | { type: 'name'; value: string }
  | { type: 'string'; value: string }
  | { type: 'int'; value: number }
  | { type: 'float'; value: number }
  | { type: 'spread'; value: '...' };

function tokenizeGraphql(source: string): GqlToken[] {
  const tokens: GqlToken[] = [];
  let i = 0;
  const isNameStart = (c: string): boolean => /[A-Za-z_]/.test(c);
  const isNameChar = (c: string): boolean => /[A-Za-z0-9_]/.test(c);
  while (i < source.length) {
    const c = source[i]!;
    if (c === ' ' || c === '\t' || c === '\n' || c === '\r' || c === ',' || c === '﻿') {
      i += 1;
      continue;
    }
    if (c === '#') {
      while (i < source.length && source[i] !== '\n') i += 1;
      continue;
    }
    if (c === '.' && source.slice(i, i + 3) === '...') {
      tokens.push({ type: 'spread', value: '...' });
      i += 3;
      continue;
    }
    if ('{}()[]:!=$@'.includes(c)) {
      tokens.push({ type: 'punct', value: c });
      i += 1;
      continue;
    }
    if (c === '"') {
      if (source.slice(i, i + 3) === '"""') {
        const end = source.indexOf('"""', i + 3);
        if (end < 0) throw new Error('unterminated block string');
        tokens.push({ type: 'string', value: source.slice(i + 3, end) });
        i = end + 3;
        continue;
      }
      let j = i + 1;
      let value = '';
      while (j < source.length && source[j] !== '"') {
        if (source[j] === '\\') {
          const esc = source[j + 1];
          const escapes: Record<string, string> = { n: '\n', t: '\t', r: '\r', '"': '"', '\\': '\\', '/': '/', b: '\b', f: '' };
          if (esc === 'u') {
            value += String.fromCharCode(Number.parseInt(source.slice(j + 2, j + 6), 16));
            j += 6;
          } else {
            value += escapes[esc ?? ''] ?? esc ?? '';
            j += 2;
          }
        } else {
          value += source[j];
          j += 1;
        }
      }
      if (j >= source.length) throw new Error('unterminated string');
      tokens.push({ type: 'string', value });
      i = j + 1;
      continue;
    }
    if (/[0-9-]/.test(c)) {
      let j = i;
      if (source[j] === '-') j += 1;
      let isFloat = false;
      while (j < source.length && /[0-9]/.test(source[j]!)) j += 1;
      if (source[j] === '.') {
        isFloat = true;
        j += 1;
        while (j < source.length && /[0-9]/.test(source[j]!)) j += 1;
      }
      if (source[j] === 'e' || source[j] === 'E') {
        isFloat = true;
        j += 1;
        if (source[j] === '+' || source[j] === '-') j += 1;
        while (j < source.length && /[0-9]/.test(source[j]!)) j += 1;
      }
      const num = Number(source.slice(i, j));
      tokens.push(isFloat ? { type: 'float', value: num } : { type: 'int', value: num });
      i = j;
      continue;
    }
    if (isNameStart(c)) {
      let j = i;
      while (j < source.length && isNameChar(source[j]!)) j += 1;
      tokens.push({ type: 'name', value: source.slice(i, j) });
      i = j;
      continue;
    }
    throw new Error(`unexpected character ${c}`);
  }
  return tokens;
}

class GqlParser {
  private pos = 0;
  private tokens: GqlToken[];
  constructor(tokens: GqlToken[]) { this.tokens = tokens; }

  peek(): GqlToken | undefined {
    return this.tokens[this.pos];
  }

  next(): GqlToken {
    const token = this.tokens[this.pos];
    if (!token) throw new Error('unexpected end of document');
    this.pos += 1;
    return token;
  }

  expectPunct(value: string): void {
    const token = this.next();
    if (token.type !== 'punct' || token.value !== value) throw new Error(`expected ${value}`);
  }

  matchPunct(value: string): boolean {
    const token = this.peek();
    if (token?.type === 'punct' && token.value === value) {
      this.pos += 1;
      return true;
    }
    return false;
  }

  expectName(): string {
    const token = this.next();
    if (token.type !== 'name') throw new Error('expected name');
    return token.value;
  }

  parseDocument(): GqlDocument {
    const doc: GqlDocument = { operations: [], fragments: new Map() };
    while (this.peek()) {
      const token = this.peek()!;
      if (token.type === 'punct' && token.value === '{') {
        doc.operations.push({ kind: 'query', selections: this.parseSelectionSet() });
        continue;
      }
      const keyword = this.expectName();
      if (keyword === 'query' || keyword === 'mutation' || keyword === 'subscription') {
        let name: string | undefined;
        if (this.peek()?.type === 'name') name = this.next().value as string;
        let variableDefinitions: GqlOperation['variableDefinitions'];
        if (this.peek()?.type === 'punct' && this.peek()?.value === '(') variableDefinitions = this.parseVariableDefinitions();
        const selections = this.parseSelectionSet();
        doc.operations.push({ kind: keyword as 'query' | 'mutation', name, variableDefinitions, selections });
      } else if (keyword === 'fragment') {
        const fragName = this.expectName();
        const onKeyword = this.expectName();
        if (onKeyword !== 'on') throw new Error('expected on');
        const typeCondition = this.expectName();
        void typeCondition;
        const selections = this.parseSelectionSet();
        doc.fragments.set(fragName, selections);
      } else {
        throw new Error(`unexpected keyword ${keyword}`);
      }
    }
    return doc;
  }

  parseVariableDefinitions(): { name: string; type: string; defaultValue?: GqlValue }[] {
    this.expectPunct('(');
    const defs: { name: string; type: string; defaultValue?: GqlValue }[] = [];
    while (!(this.peek()?.type === 'punct' && this.peek()?.value === ')')) {
      this.expectPunct('$');
      const name = this.expectName();
      this.expectPunct(':');
      const type = this.parseType();
      let defaultValue: GqlValue | undefined;
      if (this.matchPunct('=')) defaultValue = this.parseValue();
      defs.push({ name, type, defaultValue });
    }
    this.expectPunct(')');
    return defs;
  }

  parseType(): string {
    let type: string;
    if (this.matchPunct('[')) {
      type = `[${this.parseType()}]`;
      this.expectPunct(']');
    } else {
      type = this.expectName();
    }
    if (this.matchPunct('!')) type += '!';
    return type;
  }

  parseSelectionSet(): GqlSelection[] {
    this.expectPunct('{');
    const selections: GqlSelection[] = [];
    while (!(this.peek()?.type === 'punct' && this.peek()?.value === '}')) {
      selections.push(this.parseSelection());
    }
    this.expectPunct('}');
    return selections;
  }

  parseSelection(): GqlSelection {
    if (this.peek()?.type === 'spread') {
      this.next();
      if (this.peek()?.type === 'name' && (this.peek() as { value: string }).value === 'on') {
        this.next();
        const typeCondition = this.expectName();
        this.skipDirectives();
        return { kind: 'inlineFragment', typeCondition, selections: this.parseSelectionSet() };
      }
      const name = this.expectName();
      this.skipDirectives();
      return { kind: 'fragmentSpread', name };
    }
    let name = this.expectName();
    let alias: string | undefined;
    if (this.peek()?.type === 'punct' && this.peek()?.value === ':') {
      this.next();
      alias = name;
      name = this.expectName();
    }
    let args: { name: string; value: GqlValue }[] | undefined;
    if (this.peek()?.type === 'punct' && this.peek()?.value === '(') args = this.parseArguments();
    this.skipDirectives();
    let selections: GqlSelection[] | undefined;
    if (this.peek()?.type === 'punct' && this.peek()?.value === '{') selections = this.parseSelectionSet();
    return { kind: 'field', name, alias, args, selections };
  }

  parseArguments(): { name: string; value: GqlValue }[] {
    this.expectPunct('(');
    const args: { name: string; value: GqlValue }[] = [];
    while (!(this.peek()?.type === 'punct' && this.peek()?.value === ')')) {
      const name = this.expectName();
      this.expectPunct(':');
      args.push({ name, value: this.parseValue() });
    }
    this.expectPunct(')');
    return args;
  }

  parseValue(): GqlValue {
    const token = this.next();
    if (token.type === 'punct' && token.value === '$') return { kind: 'variable', name: this.expectName() };
    if (token.type === 'punct' && token.value === '[') {
      const values: GqlValue[] = [];
      while (!(this.peek()?.type === 'punct' && this.peek()?.value === ']')) values.push(this.parseValue());
      this.expectPunct(']');
      return { kind: 'list', values };
    }
    if (token.type === 'punct' && token.value === '{') {
      const fields: { name: string; value: GqlValue }[] = [];
      while (!(this.peek()?.type === 'punct' && this.peek()?.value === '}')) {
        const name = this.expectName();
        this.expectPunct(':');
        fields.push({ name, value: this.parseValue() });
      }
      this.expectPunct('}');
      return { kind: 'object', fields };
    }
    if (token.type === 'string') return { kind: 'string', value: token.value };
    if (token.type === 'int' || token.type === 'float') return { kind: 'int', value: token.value };
    if (token.type === 'name') {
      if (token.value === 'true') return { kind: 'boolean', value: true };
      if (token.value === 'false') return { kind: 'boolean', value: false };
      if (token.value === 'null') return { kind: 'null' };
      return { kind: 'enum', value: token.value };
    }
    throw new Error('unexpected value');
  }

  skipDirectives(): void {
    while (this.peek()?.type === 'punct' && this.peek()?.value === '@') {
      this.next();
      this.expectName();
      if (this.peek()?.type === 'punct' && this.peek()?.value === '(') this.parseArguments();
    }
  }
}

// ---------------------------------------------------------------------------
// GraphQL: executor
// ---------------------------------------------------------------------------

interface GqlNode {
  __typename: string;
  field(name: string, args: Record<string, unknown>): unknown;
}

function isGqlNode(value: unknown): value is GqlNode {
  return typeof value === 'object' && value !== null && '__typename' in value && typeof (value as GqlNode).field === 'function';
}

function resolveGqlValue(value: GqlValue, variables: Record<string, unknown>): unknown {
  switch (value.kind) {
    case 'variable':
      return variables[value.name];
    case 'string':
    case 'int':
    case 'boolean':
      return value.value;
    case 'enum':
      return value.value;
    case 'null':
      return null;
    case 'list':
      return value.values.map((entry) => resolveGqlValue(entry, variables));
    case 'object': {
      const out: Record<string, unknown> = {};
      for (const field of value.fields) out[field.name] = resolveGqlValue(field.value, variables);
      return out;
    }
  }
}

function executeSelections(selections: GqlSelection[], node: GqlNode, fragments: Map<string, GqlSelection[]>, variables: Record<string, unknown>, errors: { message: string }[]): Record<string, unknown> {
  const result: Record<string, unknown> = {};
  for (const selection of selections) {
    if (selection.kind === 'fragmentSpread') {
      const fragment = fragments.get(selection.name!);
      if (!fragment) {
        errors.push({ message: `Unknown fragment "${selection.name}".` });
        continue;
      }
      Object.assign(result, executeSelections(fragment, node, fragments, variables, errors));
      continue;
    }
    if (selection.kind === 'inlineFragment') {
      if (selection.typeCondition && selection.typeCondition !== node.__typename) continue;
      Object.assign(result, executeSelections(selection.selections ?? [], node, fragments, variables, errors));
      continue;
    }
    const fieldName = selection.name!;
    if (fieldName === '__typename') {
      result[selection.alias ?? fieldName] = node.__typename;
      continue;
    }
    if (!schemaHasField(node.__typename, fieldName)) {
      errors.push({ message: `Cannot query field "${fieldName}" on type "${node.__typename}".` });
      continue;
    }
    const args: Record<string, unknown> = {};
    for (const arg of selection.args ?? []) args[arg.name] = resolveGqlValue(arg.value, variables);
    let raw: unknown;
    try {
      raw = node.field(fieldName, args);
    } catch (err) {
      errors.push({ message: (err as Error).message });
      result[selection.alias ?? fieldName] = null;
      continue;
    }
    result[selection.alias ?? fieldName] = resolveFieldValue(raw, selection.selections, fragments, variables, errors);
  }
  return result;
}

function resolveFieldValue(raw: unknown, selections: GqlSelection[] | undefined, fragments: Map<string, GqlSelection[]>, variables: Record<string, unknown>, errors: { message: string }[]): unknown {
  if (raw === null || raw === undefined) return null;
  if (Array.isArray(raw)) return raw.map((item) => resolveFieldValue(item, selections, fragments, variables, errors));
  if (isGqlNode(raw)) {
    if (!selections || selections.length === 0) return null;
    return executeSelections(selections, raw, fragments, variables, errors);
  }
  return raw;
}

// ---------------------------------------------------------------------------
// GraphQL: node implementations
// ---------------------------------------------------------------------------

function encodeCursor(number: number): string {
  return Buffer.from(`cursor:${number}`, 'utf8').toString('base64');
}

function decodeCursor(cursor: string): number | null {
  try {
    const text = Buffer.from(cursor, 'base64').toString('utf8');
    if (!text.startsWith('cursor:')) return null;
    const parsed = Number.parseInt(text.slice(7), 10);
    return Number.isNaN(parsed) ? null : parsed;
  } catch {
    return null;
  }
}

interface PageInfoData {
  hasNextPage: boolean;
  startCursor: string | null;
  endCursor: string | null;
}

class PageInfoNode implements GqlNode {
  __typename = 'PageInfo';
  private data: PageInfoData;
  constructor(data: PageInfoData) { this.data = data; }
  field(name: string): unknown {
    switch (name) {
      case 'hasNextPage':
        return this.data.hasNextPage;
      case 'hasPreviousPage':
        return false;
      case 'startCursor':
        return this.data.startCursor;
      case 'endCursor':
        return this.data.endCursor;
      default:
        return null;
    }
  }
}

class EdgeNode implements GqlNode {
  __typename: string;
  private node: GqlNode;
  private cursorValue: string;
  constructor(node: GqlNode, cursorValue: string) {
    this.__typename = `${node.__typename}Edge`;
    this.node = node;
    this.cursorValue = cursorValue;
  }
  field(name: string): unknown {
    if (name === 'node') return this.node;
    if (name === 'cursor') return this.cursorValue;
    return null;
  }
}

class ConnectionNode implements GqlNode {
  __typename: string;
  private items: { node: GqlNode; cursor: string }[];
  private pageInfoData: PageInfoData;
  private total: number;
  constructor(typename: string, items: { node: GqlNode; cursor: string }[], pageInfoData: PageInfoData, total: number) {
    this.__typename = typename;
    this.items = items;
    this.pageInfoData = pageInfoData;
    this.total = total;
  }
  field(name: string): unknown {
    switch (name) {
      case 'nodes':
        return this.items.map((item) => item.node);
      case 'edges':
        return this.items.map((item) => new EdgeNode(item.node, item.cursor));
      case 'totalCount':
        return this.total;
      case 'pageInfo':
        return new PageInfoNode(this.pageInfoData);
      default:
        return null;
    }
  }
}

function connectionFrom<T>(typename: string, all: T[], toNode: (item: T) => GqlNode, cursorOf: (item: T) => number, args: Record<string, unknown>): ConnectionNode {
  const first = typeof args.first === 'number' ? Math.max(0, args.first) : 30;
  const after = typeof args.after === 'string' ? decodeCursor(args.after) : null;
  let list = [...all];
  if (after !== null) list = list.filter((item) => cursorOf(item) > after);
  const page = list.slice(0, first);
  const hasNextPage = list.length > page.length;
  const startCursor = page.length ? encodeCursor(cursorOf(page[0]!)) : null;
  const endCursor = page.length ? encodeCursor(cursorOf(page[page.length - 1]!)) : null;
  return new ConnectionNode(typename, page.map((item) => ({ node: toNode(item), cursor: encodeCursor(cursorOf(item)) })), { hasNextPage, startCursor, endCursor }, all.length);
}

class UserNode implements GqlNode {
  __typename = 'User';
  field(name: string): unknown {
    switch (name) {
      case 'login':
        return VIEWER_LOGIN;
      case 'id':
        return VIEWER_ID;
      case 'name':
        return VIEWER_NAME;
      case 'email':
        return VIEWER_EMAIL;
      case 'url':
        return `https://example.invalid/${VIEWER_LOGIN}`;
      default:
        return null;
    }
  }
}

class GitObjectNode implements GqlNode {
  __typename = 'GitObject';
  private oid: string;
  private typeName: string;
  constructor(oid: string, typeName: string) { this.oid = oid; this.typeName = typeName; }
  field(name: string): unknown {
    if (name === 'oid') return this.oid;
    if (name === 'type') return this.typeName;
    return null;
  }
}

class BranchNode implements GqlNode {
  __typename = 'Ref';
  private repo: Repo;
  private branchName: string;
  private oid: string;
  constructor(repo: Repo, branchName: string, oid: string) { this.repo = repo; this.branchName = branchName; this.oid = oid; }
  field(name: string): unknown {
    if (name === 'name') return this.branchName;
    if (name === 'target') {
      const object = this.repo.objects.get(this.oid);
      return new GitObjectNode(this.oid, object?.type ?? 'commit');
    }
    return null;
  }
}

class IssueNode implements GqlNode {
  __typename = 'Issue';
  private repo: Repo;
  private issue: Issue;
  constructor(repo: Repo, issue: Issue) { this.repo = repo; this.issue = issue; }
  field(name: string, args: Record<string, unknown>): unknown {
    switch (name) {
      case 'id':
        return issueGlobalId(this.repo, this.issue);
      case 'databaseId':
        return this.issue.id;
      case 'number':
        return this.issue.number;
      case 'title':
        return this.issue.title;
      case 'body':
        return this.issue.body;
      case 'state':
        return this.issue.state === 'open' ? 'OPEN' : 'CLOSED';
      case 'url':
        return `https://example.invalid/${this.repo.owner}/${this.repo.name}/issues/${this.issue.number}`;
      case 'author':
        return new UserNode();
      case 'repository':
        return new RepositoryNode(this.repo);
      case 'createdAt':
      case 'updatedAt':
        return FIXED_TS;
      case 'comments': {
        const comments = this.repo.comments.get(this.issue.number) ?? [];
        return connectionFrom('IssueCommentConnection', comments, (comment) => new CommentNode(this.repo, this.issue.number, comment), (comment) => comment.id, args);
      }
      default:
        return null;
    }
  }
}

class CommentNode implements GqlNode {
  __typename = 'IssueComment';
  private repo: Repo;
  private issueNumber: number;
  private comment: IssueComment;
  constructor(repo: Repo, issueNumber: number, comment: IssueComment) { this.repo = repo; this.issueNumber = issueNumber; this.comment = comment; }
  field(name: string): unknown {
    switch (name) {
      case 'id':
        return commentGlobalId(this.repo, this.issueNumber, this.comment);
      case 'databaseId':
        return this.comment.id;
      case 'body':
        return this.comment.body;
      case 'author':
        return new UserNode();
      case 'createdAt':
      case 'updatedAt':
        return FIXED_TS;
      default:
        return null;
    }
  }
}

class PullRequestFileNode implements GqlNode {
  __typename = 'PullRequestFile';
  private change: FileChange;
  constructor(change: FileChange) { this.change = change; }
  field(name: string): unknown {
    switch (name) {
      case 'path':
      case 'filename':
        return this.change.path;
      case 'additions':
        return this.change.additions;
      case 'deletions':
        return this.change.deletions;
      case 'changes':
        return this.change.changes;
      case 'changeType':
        return this.change.status === 'added' ? 'ADDED' : this.change.status === 'removed' ? 'REMOVED' : 'MODIFIED';
      case 'status':
        return this.change.status;
      default:
        return null;
    }
  }
}

class PullRequestNode implements GqlNode {
  __typename = 'PullRequest';
  private repo: Repo;
  private pull: Pull;
  constructor(repo: Repo, pull: Pull) { this.repo = repo; this.pull = pull; }
  field(name: string, args: Record<string, unknown>): unknown {
    switch (name) {
      case 'id':
        return pullGlobalId(this.repo, this.pull);
      case 'databaseId':
        return this.pull.id;
      case 'number':
        return this.pull.number;
      case 'title':
        return this.pull.title;
      case 'body':
        return this.pull.body;
      case 'state':
        return this.pull.merged ? 'MERGED' : this.pull.state === 'open' ? 'OPEN' : 'CLOSED';
      case 'merged':
        return this.pull.merged;
      case 'mergeable':
        return mergeableState(this.repo, this.pull);
      case 'headRefName':
        return this.pull.headRef;
      case 'baseRefName':
        return this.pull.baseRef;
      case 'headRefOid':
        return this.pull.headSha;
      case 'baseRefOid':
        return this.pull.baseSha;
      case 'url':
        return `https://example.invalid/${this.repo.owner}/${this.repo.name}/pull/${this.pull.number}`;
      case 'author':
        return new UserNode();
      case 'repository':
        return new RepositoryNode(this.repo);
      case 'createdAt':
      case 'updatedAt':
        return FIXED_TS;
      case 'files': {
        const base = mergeBase(this.repo, this.pull.baseSha, this.pull.headSha) ?? this.pull.baseSha;
        const files = diffTrees(this.repo, treeOfCommit(this.repo, base), treeOfCommit(this.repo, this.pull.headSha));
        return connectionFrom('PullRequestFileConnection', files, (change) => new PullRequestFileNode(change), (_change) => 0, args);
      }
      default:
        return null;
    }
  }
}

class RepositoryNode implements GqlNode {
  __typename = 'Repository';
  private repo: Repo;
  constructor(repo: Repo) { this.repo = repo; }
  field(name: string, args: Record<string, unknown>): unknown {
    switch (name) {
      case 'id':
        return repoGlobalId(this.repo);
      case 'databaseId':
        return this.repo.id;
      case 'name':
        return this.repo.name;
      case 'nameWithOwner':
        return `${this.repo.owner}/${this.repo.name}`;
      case 'owner':
        return new UserNode();
      case 'description':
        return this.repo.description;
      case 'url':
        return `https://example.invalid/${this.repo.owner}/${this.repo.name}`;
      case 'defaultBranchRef': {
        const tip = this.repo.refs.get(`refs/heads/${this.repo.defaultBranch}`);
        if (tip === undefined) return null;
        return new BranchNode(this.repo, this.repo.defaultBranch, tip);
      }
      case 'viewerPermission':
        return 'ADMIN';
      case 'hasIssuesEnabled':
        return true;
      case 'createdAt':
      case 'updatedAt':
        return FIXED_TS;
      case 'issue': {
        const number = args.number as number;
        const issue = this.repo.issues.find((entry) => entry.number === number);
        return issue ? new IssueNode(this.repo, issue) : null;
      }
      case 'issues': {
        const states = Array.isArray(args.states) ? (args.states as string[]) : null;
        let list = [...this.repo.issues];
        if (states !== null) list = list.filter((issue) => states.includes(issue.state === 'open' ? 'OPEN' : 'CLOSED'));
        const orderBy = asRecord(args.orderBy);
        const direction = orderBy?.direction === 'ASC' ? 'ASC' : 'DESC';
        list.sort((a, b) => {
          const primary = direction === 'ASC' ? a.seq - b.seq : b.seq - a.seq;
          return primary !== 0 ? primary : b.number - a.number;
        });
        const after = typeof args.after === 'string' ? decodeCursor(args.after) : null;
        if (after !== null) list = direction === 'ASC' ? list.filter((issue) => issue.number > after) : list.filter((issue) => issue.number < after);
        const first = typeof args.first === 'number' ? Math.max(0, args.first) : 30;
        const page = list.slice(0, first);
        const hasNextPage = list.length > page.length;
        const startCursor = page.length ? encodeCursor(page[0]!.number) : null;
        const endCursor = page.length ? encodeCursor(page[page.length - 1]!.number) : null;
        return new ConnectionNode('IssueConnection', page.map((issue) => ({ node: new IssueNode(this.repo, issue), cursor: encodeCursor(issue.number) })), { hasNextPage, startCursor, endCursor }, this.repo.issues.length);
      }
      case 'pullRequest': {
        const number = args.number as number;
        const pull = this.repo.pulls.find((entry) => entry.number === number);
        return pull ? new PullRequestNode(this.repo, pull) : null;
      }
      case 'pullRequests': {
        const states = Array.isArray(args.states) ? (args.states as string[]) : null;
        let list = [...this.repo.pulls];
        if (states !== null) {
          list = list.filter((pull) => {
            const state = pull.merged ? 'MERGED' : pull.state === 'open' ? 'OPEN' : 'CLOSED';
            return states.includes(state);
          });
        }
        const orderBy = asRecord(args.orderBy);
        const direction = orderBy?.direction === 'ASC' ? 'ASC' : 'DESC';
        list.sort((a, b) => {
          const primary = direction === 'ASC' ? a.seq - b.seq : b.seq - a.seq;
          return primary !== 0 ? primary : b.number - a.number;
        });
        const after = typeof args.after === 'string' ? decodeCursor(args.after) : null;
        if (after !== null) list = direction === 'ASC' ? list.filter((pull) => pull.number > after) : list.filter((pull) => pull.number < after);
        const first = typeof args.first === 'number' ? Math.max(0, args.first) : 30;
        const page = list.slice(0, first);
        const hasNextPage = list.length > page.length;
        const startCursor = page.length ? encodeCursor(page[0]!.number) : null;
        const endCursor = page.length ? encodeCursor(page[page.length - 1]!.number) : null;
        return new ConnectionNode('PullRequestConnection', page.map((pull) => ({ node: new PullRequestNode(this.repo, pull), cursor: encodeCursor(pull.number) })), { hasNextPage, startCursor, endCursor }, this.repo.pulls.length);
      }
      default:
        return null;
    }
  }
}

function repoFromGlobalId(id: string): Repo | null {
  const decoded = decodeId(id);
  if (!decoded || decoded.kind !== 'R') return null;
  const [owner, name] = decoded.value.split('/');
  if (owner === undefined || name === undefined) return null;
  return findRepo(owner, name);
}

function issueFromGlobalId(id: string): { repo: Repo; issue: Issue } | null {
  const decoded = decodeId(id);
  if (!decoded || decoded.kind !== 'I') return null;
  const [ownerName, numberText] = decoded.value.split(':');
  const [owner, name] = (ownerName ?? '').split('/');
  if (owner === undefined || name === undefined) return null;
  const repo = findRepo(owner, name);
  if (!repo) return null;
  const issue = repo.issues.find((entry) => entry.number === Number(numberText));
  return issue ? { repo, issue } : null;
}

function pullFromGlobalId(id: string): { repo: Repo; pull: Pull } | null {
  const decoded = decodeId(id);
  if (!decoded || decoded.kind !== 'P') return null;
  const [ownerName, numberText] = decoded.value.split(':');
  const [owner, name] = (ownerName ?? '').split('/');
  if (owner === undefined || name === undefined) return null;
  const repo = findRepo(owner, name);
  if (!repo) return null;
  const pull = repo.pulls.find((entry) => entry.number === Number(numberText));
  return pull ? { repo, pull } : null;
}

class CreateIssuePayloadNode implements GqlNode {
  __typename = 'CreateIssuePayload';
  private repo: Repo;
  private issue: Issue;
  constructor(repo: Repo, issue: Issue) { this.repo = repo; this.issue = issue; }
  field(name: string): unknown {
    if (name === 'issue') return new IssueNode(this.repo, this.issue);
    if (name === 'clientMutationId') return null;
    return null;
  }
}

class CloseIssuePayloadNode implements GqlNode {
  __typename = 'CloseIssuePayload';
  private repo: Repo;
  private issue: Issue;
  constructor(repo: Repo, issue: Issue) { this.repo = repo; this.issue = issue; }
  field(name: string): unknown {
    if (name === 'issue') return new IssueNode(this.repo, this.issue);
    if (name === 'clientMutationId') return null;
    return null;
  }
}

class CreatePullRequestPayloadNode implements GqlNode {
  __typename = 'CreatePullRequestPayload';
  private repo: Repo;
  private pull: Pull;
  constructor(repo: Repo, pull: Pull) { this.repo = repo; this.pull = pull; }
  field(name: string): unknown {
    if (name === 'pullRequest') return new PullRequestNode(this.repo, this.pull);
    if (name === 'clientMutationId') return null;
    return null;
  }
}

class MergePullRequestPayloadNode implements GqlNode {
  __typename = 'MergePullRequestPayload';
  private repo: Repo;
  private pull: Pull;
  constructor(repo: Repo, pull: Pull) { this.repo = repo; this.pull = pull; }
  field(name: string): unknown {
    if (name === 'pullRequest') return new PullRequestNode(this.repo, this.pull);
    if (name === 'clientMutationId') return null;
    return null;
  }
}

class AddCommentPayloadNode implements GqlNode {
  __typename = 'AddCommentPayload';
  private repo: Repo;
  private issueNumber: number;
  private comment: IssueComment;
  constructor(repo: Repo, issueNumber: number, comment: IssueComment) { this.repo = repo; this.issueNumber = issueNumber; this.comment = comment; }
  field(name: string): unknown {
    if (name === 'commentEdge') return new EdgeNode(new CommentNode(this.repo, this.issueNumber, this.comment), encodeCursor(this.comment.id));
    if (name === 'comment') return new CommentNode(this.repo, this.issueNumber, this.comment);
    if (name === 'subject') {
      const issue = this.repo.issues.find((entry) => entry.number === this.issueNumber);
      return issue ? new IssueNode(this.repo, issue) : null;
    }
    if (name === 'clientMutationId') return null;
    return null;
  }
}

class MutationNode implements GqlNode {
  __typename = 'Mutation';
  field(name: string, args: Record<string, unknown>): unknown {
    const input = asRecord(args.input) ?? {};
    switch (name) {
      case 'createIssue': {
        const repo = repoFromGlobalId(strField(input, 'repositoryId'));
        if (!repo) throw new Error('repository not found');
        const title = strField(input, 'title');
        if (title === '') throw new Error('title is required');
        const created = createIssueInRepo(repo, title, strField(input, 'body'), []);
        if ('error' in created) throw new Error(created.error);
        return new CreateIssuePayloadNode(repo, created);
      }
      case 'closeIssue': {
        const found = issueFromGlobalId(strField(input, 'issueId'));
        if (!found) throw new Error('issue not found');
        found.issue.state = 'closed';
        return new CloseIssuePayloadNode(found.repo, found.issue);
      }
      case 'createPullRequest': {
        const repo = repoFromGlobalId(strField(input, 'repositoryId'));
        if (!repo) throw new Error('repository not found');
        const created = createPullInRepo(repo, strField(input, 'title'), strField(input, 'body'), strField(input, 'headRefName'), strField(input, 'baseRefName'));
        if ('error' in created) throw new Error(created.error);
        return new CreatePullRequestPayloadNode(repo, created);
      }
      case 'mergePullRequest': {
        const found = pullFromGlobalId(strField(input, 'pullRequestId'));
        if (!found) throw new Error('pull request not found');
        const merged = mergePullInRepo(found.repo, found.pull);
        if ('error' in merged) throw new Error(merged.error);
        return new MergePullRequestPayloadNode(found.repo, found.pull);
      }
      case 'addComment': {
        const found = issueFromGlobalId(strField(input, 'subjectId'));
        if (!found) throw new Error('subject not found');
        const text = strField(input, 'body');
        if (text === '') throw new Error('body is required');
        const comment: IssueComment = { id: found.repo.nextComment++, body: text };
        const list = found.repo.comments.get(found.issue.number) ?? [];
        list.push(comment);
        found.repo.comments.set(found.issue.number, list);
        return new AddCommentPayloadNode(found.repo, found.issue.number, comment);
      }
      default:
        return null;
    }
  }
}

class QueryNode implements GqlNode {
  __typename = 'Query';
  field(name: string, args: Record<string, unknown>): unknown {
    switch (name) {
      case 'viewer':
        return new UserNode();
      case 'repository': {
        const owner = typeof args.owner === 'string' ? args.owner : '';
        const repoName = typeof args.name === 'string' ? args.name : '';
        const repo = findRepo(owner, repoName);
        return repo ? new RepositoryNode(repo) : null;
      }
      case 'node': {
        const id = typeof args.id === 'string' ? args.id : '';
        const decoded = decodeId(id);
        if (!decoded) return null;
        if (decoded.kind === 'R') {
          const repo = repoFromGlobalId(id);
          return repo ? new RepositoryNode(repo) : null;
        }
        if (decoded.kind === 'I') {
          const found = issueFromGlobalId(id);
          return found ? new IssueNode(found.repo, found.issue) : null;
        }
        if (decoded.kind === 'P') {
          const found = pullFromGlobalId(id);
          return found ? new PullRequestNode(found.repo, found.pull) : null;
        }
        return null;
      }
      case 'search':
        return new ConnectionNode('SearchResultItemConnection', [], { hasNextPage: false, startCursor: null, endCursor: null }, 0);
      case '__type': {
        const typeName = typeof args.name === 'string' ? args.name : '';
        const desc = SCHEMA[typeName];
        return desc ? new TypeRefNode({ kind: 'NAMED', name: desc.name }) : null;
      }
      case '__schema':
        return new SchemaNode();
      default:
        return null;
    }
  }
}

// ---------------------------------------------------------------------------
// GraphQL: introspection nodes
// ---------------------------------------------------------------------------

interface TypeRef {
  kind: 'NAMED' | 'LIST' | 'NON_NULL';
  name?: string;
  ofType?: TypeRef;
}

function parseTypeRef(type: string): TypeRef {
  if (type.endsWith('!')) return { kind: 'NON_NULL', ofType: parseTypeRef(type.slice(0, -1)) };
  if (type.startsWith('[') && type.endsWith(']')) return { kind: 'LIST', ofType: parseTypeRef(type.slice(1, -1)) };
  return { kind: 'NAMED', name: type };
}

class TypeRefNode implements GqlNode {
  __typename = '__Type';
  private ref: TypeRef;
  constructor(ref: TypeRef) { this.ref = ref; }
  field(name: string, args: Record<string, unknown>): unknown {
    switch (name) {
      case 'name':
        return this.ref.kind === 'NAMED' ? this.ref.name ?? null : null;
      case 'kind':
        return this.ref.kind;
      case 'description':
        return null;
      case 'fields': {
        if (this.ref.kind !== 'NAMED') return null;
        const desc = SCHEMA[this.ref.name ?? ''];
        const includeDeprecated = args.includeDeprecated === true;
        return (desc?.fields ?? []).filter((field) => includeDeprecated || !field.deprecated).map((field) => new FieldNode(field));
      }
      case 'enumValues': {
        if (this.ref.kind !== 'NAMED') return null;
        const desc = SCHEMA[this.ref.name ?? ''];
        const includeDeprecated = args.includeDeprecated === true;
        return (desc?.enumValues ?? []).filter((value) => includeDeprecated || !value.deprecated).map((value) => new EnumValueNode(value));
      }
      case 'inputFields': {
        if (this.ref.kind !== 'NAMED') return null;
        const desc = SCHEMA[this.ref.name ?? ''];
        return (desc?.inputFields ?? []).map((field) => new InputValueNode(field.name, field.type));
      }
      case 'interfaces':
        return [];
      case 'possibleTypes':
        return [];
      case 'ofType':
        return this.ref.ofType ? new TypeRefNode(this.ref.ofType) : null;
      case 'specifiedByURL':
        return null;
      default:
        return null;
    }
  }
}

class FieldNode implements GqlNode {
  __typename = '__Field';
  private fieldDesc: FieldDesc;
  constructor(fieldDesc: FieldDesc) { this.fieldDesc = fieldDesc; }
  field(name: string): unknown {
    switch (name) {
      case 'name':
        return this.fieldDesc.name;
      case 'description':
        return null;
      case 'args':
        return (this.fieldDesc.args ?? []).map((arg) => new InputValueNode(arg.name, arg.type, arg.defaultValue));
      case 'type':
        return new TypeRefNode(parseTypeRef(this.fieldDesc.type));
      case 'isDeprecated':
        return false;
      case 'deprecationReason':
        return null;
      default:
        return null;
    }
  }
}

class InputValueNode implements GqlNode {
  __typename = '__InputValue';
  private nameValue: string;
  private typeValue: string;
  private defaultValue: unknown;
  constructor(nameValue: string, typeValue: string, defaultValue?: unknown) { this.nameValue = nameValue; this.typeValue = typeValue; this.defaultValue = defaultValue; }
  field(name: string): unknown {
    switch (name) {
      case 'name':
        return this.nameValue;
      case 'description':
        return null;
      case 'type':
        return new TypeRefNode(parseTypeRef(this.typeValue));
      case 'defaultValue':
        return this.defaultValue === undefined ? null : JSON.stringify(this.defaultValue);
      default:
        return null;
    }
  }
}

class EnumValueNode implements GqlNode {
  __typename = '__EnumValue';
  private value: { name: string; deprecated?: boolean };
  constructor(value: { name: string; deprecated?: boolean }) { this.value = value; }
  field(name: string): unknown {
    switch (name) {
      case 'name':
        return this.value.name;
      case 'description':
        return null;
      case 'isDeprecated':
        return false;
      case 'deprecationReason':
        return null;
      default:
        return null;
    }
  }
}

class SchemaNode implements GqlNode {
  __typename = '__Schema';
  field(name: string): unknown {
    switch (name) {
      case 'types':
        return Object.values(SCHEMA).map((desc) => new TypeRefNode({ kind: 'NAMED', name: desc.name }));
      case 'queryType':
        return new TypeRefNode({ kind: 'NAMED', name: 'Query' });
      case 'mutationType':
        return new TypeRefNode({ kind: 'NAMED', name: 'Mutation' });
      case 'subscriptionType':
        return null;
      case 'directives':
        return [];
      case 'description':
        return null;
      default:
        return null;
    }
  }
}

// ---------------------------------------------------------------------------
// GraphQL: document execution + HTTP handler
// ---------------------------------------------------------------------------

function executeGraphqlDocument(document: unknown): { data: unknown; errors?: { message: string }[] } {
  const record = asRecord(document);
  if (!record || typeof record.query !== 'string') {
    return { data: null, errors: [{ message: 'query is required' }] };
  }
  const variables = asRecord(record.variables) ?? {};
  let gqlDoc: GqlDocument;
  try {
    gqlDoc = new GqlParser(tokenizeGraphql(record.query)).parseDocument();
  } catch (err) {
    return { data: null, errors: [{ message: `GraphQL syntax error: ${(err as Error).message}` }] };
  }
  const operationName = typeof record.operationName === 'string' ? record.operationName : undefined;
  const operation = operationName !== undefined
    ? gqlDoc.operations.find((entry) => entry.name === operationName)
    : gqlDoc.operations[0];
  if (!operation) {
    return { data: null, errors: [{ message: 'operation not found' }] };
  }
  const varValues: Record<string, unknown> = { ...variables };
  for (const definition of operation.variableDefinitions ?? []) {
    if (varValues[definition.name] === undefined && definition.defaultValue !== undefined) {
      varValues[definition.name] = resolveGqlValue(definition.defaultValue, varValues);
    }
  }
  const root: GqlNode = operation.kind === 'mutation' ? new MutationNode() : new QueryNode();
  const errors: { message: string }[] = [];
  const data = executeSelections(operation.selections, root, gqlDoc.fragments, varValues, errors);
  const out: { data: unknown; errors?: { message: string }[] } = { data };
  if (errors.length) out.errors = errors;
  return out;
}

async function handleGraphql(req: IncomingMessage, res: ServerResponse): Promise<void> {
  if (!requireAuth(req, res)) return;
  const body = await readBody(req);
  let parsed: unknown;
  try {
    parsed = JSON.parse(body.toString('utf8'));
  } catch {
    sendError(res, 400, 'Problems parsing JSON');
    return;
  }
  if (Array.isArray(parsed)) {
    sendJson(res, 200, parsed.map((document) => executeGraphqlDocument(document)));
    return;
  }
  sendJson(res, 200, executeGraphqlDocument(parsed));
}

// ---------------------------------------------------------------------------
// MCP (JSON-RPC 2.0 Streamable HTTP)
// ---------------------------------------------------------------------------

const SERVER_INFO = { name: 'github-core-clone', version: '1.0.0' };

interface McpToolDef {
  name: string;
  description: string;
  inputSchema: {
    type: 'object';
    properties: Record<string, Record<string, unknown>>;
    required?: string[];
  };
}

const MCP_TOOLS: McpToolDef[] = [
  {
    name: 'create_repo',
    description: 'Create a new repository for the authenticated user.',
    inputSchema: {
      type: 'object',
      properties: {
        name: { type: 'string', description: 'Repository name.' },
        description: { type: 'string', description: 'Repository description.' },
        private: { type: 'boolean', description: 'Whether the repository is private.' },
        owner: { type: 'string', description: 'Owner login (defaults to the authenticated user).' },
      },
      required: ['name'],
    },
  },
  {
    name: 'get_repo',
    description: 'Get a repository by owner and name.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'Repository owner login.' },
        repo: { type: 'string', description: 'Repository name.' },
      },
      required: ['owner', 'repo'],
    },
  },
  {
    name: 'create_issue',
    description: 'Create an issue in a repository.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'Repository owner login.' },
        repo: { type: 'string', description: 'Repository name.' },
        title: { type: 'string', description: 'Issue title.' },
        body: { type: 'string', description: 'Issue body.' },
      },
      required: ['owner', 'repo', 'title'],
    },
  },
  {
    name: 'list_issues',
    description: 'List issues in a repository.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'Repository owner login.' },
        repo: { type: 'string', description: 'Repository name.' },
        state: { type: 'string', enum: ['open', 'closed', 'all'], description: 'Issue state filter.' },
      },
      required: ['owner', 'repo'],
    },
  },
  {
    name: 'create_pull_request',
    description: 'Create a pull request in a repository.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'Repository owner login.' },
        repo: { type: 'string', description: 'Repository name.' },
        title: { type: 'string', description: 'Pull request title.' },
        body: { type: 'string', description: 'Pull request body.' },
        head: { type: 'string', description: 'Head branch name.' },
        base: { type: 'string', description: 'Base branch name.' },
      },
      required: ['owner', 'repo', 'title', 'head', 'base'],
    },
  },
  {
    name: 'merge_pull_request',
    description: 'Merge a pull request in a repository.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'Repository owner login.' },
        repo: { type: 'string', description: 'Repository name.' },
        pull_number: { type: 'integer', description: 'Pull request number.' },
      },
      required: ['owner', 'repo', 'pull_number'],
    },
  },
];

interface McpToolResult {
  content: { type: string; text: string }[];
  structuredContent: unknown;
  isError?: boolean;
}

function callMcpTool(name: string, args: Record<string, unknown>): McpToolResult {
  const textResult = (structured: unknown, isError = false): McpToolResult => ({
    content: [{ type: 'text', text: JSON.stringify(structured) }],
    structuredContent: structured,
    ...(isError ? { isError: true } : {}),
  });
  switch (name) {
    case 'create_repo': {
      const repoName = strField(args, 'name');
      if (repos.has(repoKey(VIEWER_LOGIN, repoName))) {
        return textResult({ error: 'name already exists on this account' }, true);
      }
      const repo = createRepo(repoName, strField(args, 'description'), args.private === true);
      return textResult(repoJson(repo));
    }
    case 'get_repo': {
      const repo = findRepo(strField(args, 'owner'), strField(args, 'repo'));
      if (!repo) return textResult({ error: 'Repository not found' }, true);
      return textResult(repoJson(repo));
    }
    case 'create_issue': {
      const repo = findRepo(strField(args, 'owner'), strField(args, 'repo'));
      if (!repo) return textResult({ error: 'Repository not found' }, true);
      const created = createIssueInRepo(repo, strField(args, 'title'), strField(args, 'body'), []);
      if ('error' in created) return textResult({ error: created.error }, true);
      return textResult(issueJson(repo, created));
    }
    case 'list_issues': {
      const repo = findRepo(strField(args, 'owner'), strField(args, 'repo'));
      if (!repo) return textResult({ error: 'Repository not found' }, true);
      const state = typeof args.state === 'string' ? args.state : 'open';
      const query = new URLSearchParams();
      query.set('state', state);
      const issues = listIssuesFiltered(repo, query).map((issue) => issueJson(repo, issue));
      return textResult({ issues });
    }
    case 'create_pull_request': {
      const repo = findRepo(strField(args, 'owner'), strField(args, 'repo'));
      if (!repo) return textResult({ error: 'Repository not found' }, true);
      const created = createPullInRepo(repo, strField(args, 'title'), strField(args, 'body'), strField(args, 'head'), strField(args, 'base'));
      if ('error' in created) return textResult({ error: created.error }, true);
      return textResult(pullJson(repo, created));
    }
    case 'merge_pull_request': {
      const repo = findRepo(strField(args, 'owner'), strField(args, 'repo'));
      if (!repo) return textResult({ error: 'Repository not found' }, true);
      const number = typeof args.pull_number === 'number' ? args.pull_number : Number(args.pull_number);
      const pull = repo.pulls.find((entry) => entry.number === number);
      if (!pull) return textResult({ error: 'Pull request not found' }, true);
      const merged = mergePullInRepo(repo, pull);
      if ('error' in merged) return textResult({ error: merged.error }, true);
      return textResult({ sha: merged.sha, merged: true, number: pull.number });
    }
    default:
      return textResult({ error: `Unknown tool: ${name}` }, true);
  }
}

async function handleMcp(req: IncomingMessage, res: ServerResponse): Promise<void> {
  if (!requireAuth(req, res)) return;
  const sessionId = req.headers['mcp-session-id'];
  const extraHeaders: Record<string, string> = {};
  if (typeof sessionId === 'string' && sessionId !== '') extraHeaders['mcp-session-id'] = sessionId;
  const raw = await readBody(req);
  let parsed: unknown;
  try {
    parsed = JSON.parse(raw.toString('utf8'));
  } catch {
    sendJson(res, 400, { jsonrpc: '2.0', id: null, error: { code: -32700, message: 'Parse error' } }, extraHeaders);
    return;
  }
  const record = asRecord(parsed);
  if (!record || typeof record.method !== 'string') {
    sendJson(res, 400, { jsonrpc: '2.0', id: null, error: { code: -32600, message: 'Invalid Request' } }, extraHeaders);
    return;
  }
  const method = record.method;
  if (method.startsWith('notifications/')) {
    res.writeHead(202, { 'content-length': 0, ...extraHeaders });
    res.end();
    return;
  }
  const id = 'id' in record ? record.id : undefined;
  if (id === undefined || id === null) {
    res.writeHead(202, { 'content-length': 0, ...extraHeaders });
    res.end();
    return;
  }
  const params = asRecord(record.params) ?? {};
  const reply = (result: unknown): void => {
    sendJson(res, 200, { jsonrpc: '2.0', id, result, _meta: { 'io.modelcontextprotocol/serverInfo': SERVER_INFO } }, extraHeaders);
  };
  const replyError = (code: number, message: string): void => {
    sendJson(res, 200, { jsonrpc: '2.0', id, error: { code, message } }, extraHeaders);
  };
  switch (method) {
    case 'server/discover': {
      reply({
        supportedVersions: ['2026-07-28', '2025-11-25'],
        capabilities: { tools: {} },
        serverInfo: SERVER_INFO,
        _meta: { 'io.modelcontextprotocol/serverInfo': SERVER_INFO },
      });
      return;
    }
    case 'initialize': {
      const requested = typeof params.protocolVersion === 'string' ? params.protocolVersion : '';
      const version = requested !== '' && requested <= '2025-11-25' ? requested : '2025-11-25';
      reply({ protocolVersion: version, capabilities: { tools: {} }, serverInfo: SERVER_INFO });
      return;
    }
    case 'ping': {
      reply({});
      return;
    }
    case 'tools/list': {
      reply({ tools: MCP_TOOLS });
      return;
    }
    case 'tools/call': {
      const name = typeof params.name === 'string' ? params.name : '';
      const args = asRecord(params.arguments) ?? {};
      const tool = MCP_TOOLS.find((candidate) => candidate.name.toLowerCase() === name.toLowerCase() || name.toLowerCase().endsWith(candidate.name));
      if (!tool) {
        replyError(-32602, `Unknown tool: ${name}`);
        return;
      }
      const missing = (tool.inputSchema.required ?? []).filter((field) => args[field] === undefined || args[field] === null || args[field] === '');
      if (missing.length) {
        reply({ content: [{ type: 'text', text: `Missing required argument: ${missing.join(', ')}` }], isError: true });
        return;
      }
      reply(callMcpTool(tool.name, args));
      return;
    }
    default:
      replyError(-32601, `Method not found: ${method}`);
  }
}

// ---------------------------------------------------------------------------
// REST v3 router
// ---------------------------------------------------------------------------

async function handleRest(req: IncomingMessage, res: ServerResponse, segments: string[], query: URLSearchParams, method: string): Promise<void> {
  if (segments.length === 2) {
    if (method === 'GET') {
      sendJson(res, 200, {
        current_user_url: '/api/v3/user',
        current_user_repositories_url: '/api/v3/user/repos',
        repository_url: '/api/v3/repos/{owner}/{repo}',
        meta_url: '/api/v3/meta',
      }, { 'x-oauth-scopes': 'repo, read:org' });
      return;
    }
    sendError(res, 404, 'Not Found');
    return;
  }
  if (segments[2] === 'meta' && segments.length === 3) {
    if (method === 'GET') {
      sendJson(res, 200, { installed_version: '1.0.0' });
      return;
    }
    sendError(res, 404, 'Not Found');
    return;
  }
  if (!requireAuth(req, res)) return;
  let rawBody: Buffer | null = null;
  if (method === 'POST' || method === 'PUT' || method === 'PATCH' || method === 'DELETE') {
    rawBody = await readBody(req);
  }
  const body = rawBody === null ? {} : parseJsonBody(rawBody);
  if (segments[2] === 'user') {
    if (segments.length === 3) {
      if (method === 'GET') {
        sendJson(res, 200, { login: VIEWER_LOGIN, id: VIEWER_ID, name: VIEWER_NAME, email: VIEWER_EMAIL, type: 'User' });
        return;
      }
      sendError(res, 404, 'Not Found');
      return;
    }
    if (segments[3] === 'repos' && segments.length === 4) {
      if (method === 'GET') {
        handleListUserRepos(req, res, query);
        return;
      }
      if (method === 'POST') {
        handleCreateRepo(res, body);
        return;
      }
      sendError(res, 404, 'Not Found');
      return;
    }
    sendError(res, 404, 'Not Found');
    return;
  }
  if (segments[2] === 'repos' && segments.length >= 5) {
    const owner = segments[3]!;
    const repoName = segments[4]!;
    const repo = findRepo(owner, repoName);
    if (repo === null) {
      sendError(res, 404, 'Not Found');
      return;
    }
    const rest = segments.slice(5);
    if (rest.length === 0) {
      if (method === 'GET') {
        handleGetRepo(res, repo);
        return;
      }
      if (method === 'PATCH') {
        handlePatchRepo(res, repo, body);
        return;
      }
      if (method === 'DELETE') {
        repos.delete(repoKey(owner, repoName));
        sendJson(res, 204, null);
        return;
      }
      sendError(res, 404, 'Not Found');
      return;
    }
    if (rest[0] === 'branches') {
      if (rest.length === 1 && method === 'GET') {
        handleListBranches(res, repo);
        return;
      }
      if (rest.length === 2 && method === 'GET') {
        handleGetBranch(res, repo, rest[1]!);
        return;
      }
      sendError(res, 404, 'Not Found');
      return;
    }
    if (rest[0] === 'commits' && rest.length === 1 && method === 'GET') {
      handleListCommits(req, res, repo, query);
      return;
    }
    if (rest[0] === 'git' && rest[1] === 'refs') {
      if (rest.length === 2 && method === 'POST') {
        handleCreateGitRef(res, repo, body);
        return;
      }
      if (rest.length === 4 && rest[2] === 'heads' && method === 'GET') {
        handleGetGitRef(res, repo, rest[3]!);
        return;
      }
      sendError(res, 404, 'Not Found');
      return;
    }
    if (rest[0] === 'contents') {
      const pathSegments = rest.slice(1);
      if (method === 'PUT') {
        handlePutContents(res, repo, pathSegments, body);
        return;
      }
      if (method === 'GET') {
        handleGetContents(req, res, repo, pathSegments, query);
        return;
      }
      if (method === 'DELETE') {
        handleDeleteContents(res, repo, pathSegments, body);
        return;
      }
      sendError(res, 404, 'Not Found');
      return;
    }
    if (rest[0] === 'labels' && rest.length === 1 && method === 'POST') {
      handleCreateLabel(res, repo, body);
      return;
    }
    if (rest[0] === 'issues') {
      if (rest.length === 1) {
        if (method === 'GET') {
          handleListIssues(req, res, repo, query);
          return;
        }
        if (method === 'POST') {
          handleCreateIssue(res, repo, body);
          return;
        }
        sendError(res, 404, 'Not Found');
        return;
      }
      const issueNumber = Number.parseInt(rest[1]!, 10);
      if (Number.isNaN(issueNumber)) {
        sendError(res, 404, 'Not Found');
        return;
      }
      if (rest.length === 2) {
        if (method === 'GET') {
          handleGetIssue(res, repo, issueNumber);
          return;
        }
        if (method === 'PATCH') {
          handlePatchIssue(res, repo, issueNumber, body);
          return;
        }
        sendError(res, 404, 'Not Found');
        return;
      }
      if (rest.length === 3 && rest[2] === 'comments') {
        if (method === 'GET') {
          handleListComments(res, repo, issueNumber);
          return;
        }
        if (method === 'POST') {
          handleCreateComment(res, repo, issueNumber, body);
          return;
        }
        sendError(res, 404, 'Not Found');
        return;
      }
      sendError(res, 404, 'Not Found');
      return;
    }
    if (rest[0] === 'pulls') {
      if (rest.length === 1) {
        if (method === 'GET') {
          handleListPulls(req, res, repo, query);
          return;
        }
        if (method === 'POST') {
          handleCreatePull(res, repo, body);
          return;
        }
        sendError(res, 404, 'Not Found');
        return;
      }
      const pullNumber = Number.parseInt(rest[1]!, 10);
      if (Number.isNaN(pullNumber)) {
        sendError(res, 404, 'Not Found');
        return;
      }
      if (rest.length === 2) {
        if (method === 'GET') {
          handleGetPull(res, repo, pullNumber);
          return;
        }
        sendError(res, 404, 'Not Found');
        return;
      }
      if (rest.length === 3 && rest[2] === 'files' && method === 'GET') {
        handleListPullFiles(res, repo, pullNumber);
        return;
      }
      if (rest.length === 3 && rest[2] === 'merge' && method === 'PUT') {
        handleMergePull(res, repo, pullNumber);
        return;
      }
      sendError(res, 404, 'Not Found');
      return;
    }
    sendError(res, 404, 'Not Found');
    return;
  }
  sendError(res, 404, 'Not Found');
}

// ---------------------------------------------------------------------------
// request dispatch + app factory (main.ts owns the lifecycle)
// ---------------------------------------------------------------------------

async function handleRequest(req: IncomingMessage, res: ServerResponse): Promise<void> {
  // The request target is an origin-form path (absolute-form tolerated).
  // Split it by hand: a full WHATWG URL parse per request is pure overhead
  // on this hot path, and splitPath below does the segment decoding.
  const rawUrl = req.url ?? '/';
  let pathname = rawUrl;
  let queryString = '';
  const qmark = rawUrl.indexOf('?');
  if (qmark >= 0) {
    pathname = rawUrl.slice(0, qmark);
    queryString = rawUrl.slice(qmark + 1);
  }
  if (pathname.startsWith('http://') || pathname.startsWith('https://')) {
    const afterScheme = pathname.indexOf('://') + 3;
    const slash = pathname.indexOf('/', afterScheme);
    pathname = slash >= 0 ? pathname.slice(slash) : '/';
  }
  const query = new URLSearchParams(queryString);
  const method = req.method ?? 'GET';
  const segments = splitPath(pathname);

  if (pathname === '/healthz') {
    if (method === 'GET') {
      sendJson(res, 200, { status: 'ok' });
      return;
    }
    sendError(res, 405, 'Method not allowed');
    return;
  }
  if (pathname === '/api/graphql') {
    if (method !== 'POST') {
      sendError(res, 405, 'Method not allowed');
      return;
    }
    await handleGraphql(req, res);
    return;
  }
  if (pathname === '/mcp') {
    if (method !== 'POST') {
      sendError(res, 405, 'Method not allowed');
      return;
    }
    await handleMcp(req, res);
    return;
  }
  if (segments[0] === 'api' && segments[1] === 'v3') {
    await handleRest(req, res, segments, query, method);
    return;
  }
  if (segments.length >= 2 && segments[1]!.endsWith('.git')) {
    const owner = segments[0]!;
    const repoName = segments[1]!.slice(0, -4);
    const repo = findRepo(owner, repoName);
    if (segments[2] === 'info' && segments[3] === 'refs' && method === 'GET') {
      if (repo === null) {
        sendError(res, 404, 'Repository not found');
        return;
      }
      const service = query.get('service') ?? '';
      if (service !== 'git-upload-pack' && service !== 'git-receive-pack') {
        sendError(res, 400, 'service is required');
        return;
      }
      handleInfoRefs(req, res, repo, service);
      return;
    }
    if (segments[2] === 'git-upload-pack' && method === 'POST') {
      if (repo === null) {
        sendError(res, 404, 'Repository not found');
        return;
      }
      await handleUploadPack(req, res, repo);
      return;
    }
    if (segments[2] === 'git-receive-pack' && method === 'POST') {
      if (repo === null) {
        sendError(res, 404, 'Repository not found');
        return;
      }
      await handleReceivePack(req, res, repo);
      return;
    }
    sendError(res, 404, 'Not Found');
    return;
  }
  sendError(res, 404, 'Not Found');
}

// ---------------------------------------------------------------------------
// transport: a minimal HTTP/1.1 server on node:net
// ---------------------------------------------------------------------------
//
// node:http spends most of its per-request budget on IncomingMessage /
// ServerResponse bookkeeping: the header parser, the stream machinery, one
// writev per response part. The suite's only client is undici fetch speaking
// plain HTTP/1.1 with Content-Length bodies over keep-alive connections, so
// the forge can serve the same wire with a small purpose-built transport:
// parse the request line, headers and body straight off the socket, hand the
// handlers a narrow request/response shim, and answer with a single socket
// write. Every handler, route, status code and body is unchanged — only the
// transport moves.
//
// The whole surface the handlers touch (nothing else is provided on purpose):
//   req: .method, .url, .headers (lower-cased names), .on('data' | 'end' |
//        'error'), .destroy()
//   res: .writeHead(status, headers), .end(body?), .headersSent

/** Reason phrases for the statuses the forge sends. */
const HTTP_REASON: Record<number, string> = {
  200: 'OK',
  201: 'Created',
  202: 'Accepted',
  204: 'No Content',
  400: 'Bad Request',
  401: 'Unauthorized',
  404: 'Not Found',
  405: 'Method Not Allowed',
  409: 'Conflict',
  413: 'Content Too Large',
  422: 'Unprocessable Entity',
  500: 'Internal Server Error',
};

/** Largest request head the transport accepts before refusing the socket. */
const MAX_HEAD_BYTES = 64 * 1024;
/** Largest request body the transport buffers (readBody refuses past 64 MiB). */
const MAX_BODY_BYTES = 64 * 1024 * 1024;

/** A request head: everything before the body, with its byte length. */
interface RequestHead {
  method: string;
  url: string;
  headers: Record<string, string>;
  version: string;
  headLength: number;
  closeAfter: boolean;
}

/**
 * Parse one request head from the front of `buf`. Returns null when more
 * data is needed; throws when the wire cannot carry the request (bad framing,
 * absurd sizes).
 */
function parseHttpHead(buf: Buffer): RequestHead | null {
  const headEnd = buf.indexOf('\r\n\r\n');
  if (headEnd < 0) {
    if (buf.length > MAX_HEAD_BYTES) throw new Error('request head too large');
    return null;
  }
  if (headEnd > MAX_HEAD_BYTES) throw new Error('request head too large');
  const head = buf.subarray(0, headEnd).toString('ascii');
  const lines = head.split('\r\n');
  const requestLine = lines[0] ?? '';
  const parts = requestLine.split(' ');
  if (parts.length !== 3 || parts[0] === '' || parts[1] === '' || !(parts[2] ?? '').startsWith('HTTP/')) {
    throw new Error('malformed request line');
  }
  const headers: Record<string, string> = {};
  for (const line of lines.slice(1)) {
    const colon = line.indexOf(':');
    if (colon <= 0) throw new Error('malformed header line');
    const name = line.slice(0, colon).trim().toLowerCase();
    const value = line.slice(colon + 1).trim();
    headers[name] = headers[name] === undefined ? value : `${headers[name]}, ${value}`;
  }
  const version = parts[2]!;
  const connection = (headers['connection'] ?? '').toLowerCase();
  return {
    method: parts[0]!,
    url: parts[1]!,
    headers,
    version,
    headLength: headEnd + 4,
    closeAfter: connection.includes('close') || (version === 'HTTP/1.0' && !connection.includes('keep-alive')),
  };
}

/**
 * Read one request body from `buf` (which starts just past the head). Returns
 * the body and the bytes consumed, or null when more data is needed. Throws
 * on framing the wire cannot carry. Handles Content-Length bodies and
 * chunked transfer-encoding.
 */
function readHttpBody(head: RequestHead, buf: Buffer): { body: Buffer; consumed: number } | null {
  const chunked = (head.headers['transfer-encoding'] ?? '').toLowerCase().includes('chunked');
  if (chunked) {
    const chunks: Buffer[] = [];
    let total = 0;
    let offset = 0;
    for (;;) {
      const lineEnd = buf.indexOf('\r\n', offset);
      if (lineEnd < 0) return null;
      const sizeText = buf.subarray(offset, lineEnd).toString('ascii').trim().split(';')[0] ?? '';
      const size = Number.parseInt(sizeText, 16);
      if (!Number.isSafeInteger(size) || size < 0) throw new Error('malformed chunk size');
      offset = lineEnd + 2;
      if (size === 0) {
        // Trailers run to the next empty line.
        let at = offset;
        for (;;) {
          const lineEnd = buf.indexOf('\r\n', at);
          if (lineEnd < 0) return null;
          if (lineEnd === at) return { body: Buffer.concat(chunks, total), consumed: lineEnd + 2 };
          at = lineEnd + 2;
        }
      }
      if (offset + size + 2 > buf.length) return null;
      total += size;
      if (total > MAX_BODY_BYTES) throw new Error('request body too large');
      chunks.push(buf.subarray(offset, offset + size));
      offset += size + 2;
    }
  }
  const rawLength = head.headers['content-length'];
  const length = rawLength === undefined ? 0 : Number.parseInt(rawLength, 10);
  if (!Number.isSafeInteger(length) || length < 0) throw new Error('malformed content-length');
  if (length > MAX_BODY_BYTES) throw new Error('request body too large');
  if (buf.length < length) return null;
  return { body: Buffer.from(buf.subarray(0, length)), consumed: length };
}

/** One fully parsed request, ready for the handlers. */
interface ParsedRequest {
  method: string;
  url: string;
  headers: Record<string, string>;
  body: Buffer;
  closeAfter: boolean;
}

/** Request shim: the narrow IncomingMessage surface the handlers use. */
class ShimRequest {
  readonly method: string;
  readonly url: string;
  readonly headers: Record<string, string>;
  /** The transport already holds the whole body: readBody takes it directly. */
  readonly preBody: Buffer;
  private readonly socket: Socket;
  private destroyedFlag = false;
  private delivered = false;
  private dataListeners: Array<(chunk: Buffer) => void> = [];
  private endListeners: Array<() => void> = [];
  private errorListeners: Array<(err: Error) => void> = [];

  constructor(method: string, url: string, headers: Record<string, string>, body: Buffer, socket: Socket) {
    this.method = method;
    this.url = url;
    this.headers = headers;
    this.preBody = body;
    this.socket = socket;
  }

  on(event: 'data', listener: (chunk: Buffer) => void): this;
  on(event: 'end', listener: () => void): this;
  on(event: 'error', listener: (err: Error) => void): this;
  on(event: string, listener: (...args: never[]) => void): this {
    if (event === 'data') this.dataListeners.push(listener as (chunk: Buffer) => void);
    else if (event === 'end') this.endListeners.push(listener as () => void);
    else if (event === 'error') this.errorListeners.push(listener as (err: Error) => void);
    if (!this.delivered) {
      // Deliver on a microtask so every listener readBody registers below is
      // in place before the first one fires.
      this.delivered = true;
      queueMicrotask(() => this.deliver());
    }
    return this;
  }

  private deliver(): void {
    if (this.destroyedFlag) return;
    if (this.preBody.length > 0) for (const listener of this.dataListeners) listener(this.preBody);
    for (const listener of this.endListeners) listener();
  }

  /** Fail the request (socket died mid-flight): readBody rejects. */
  fail(err: Error): void {
    if (this.destroyedFlag) return;
    this.destroyedFlag = true;
    for (const listener of this.errorListeners) listener(err);
  }

  destroy(): void {
    this.destroyedFlag = true;
    try {
      this.socket.destroy();
    } catch {
      // The socket is already gone.
    }
  }
}

/** Response shim: the narrow ServerResponse surface the handlers use. */
class ShimResponse {
  headersSent = false;
  private status = 200;
  private headers: Record<string, string> = {};
  private done = false;
  private readonly socket: Socket;
  private readonly method: string;
  private readonly closeAfter: boolean;
  private readonly onFinished: () => void;

  constructor(socket: Socket, method: string, closeAfter: boolean, onFinished: () => void) {
    this.socket = socket;
    this.method = method;
    this.closeAfter = closeAfter;
    this.onFinished = onFinished;
  }

  writeHead(status: number, headers: Record<string, string>): void {
    this.status = status;
    this.headers = headers;
    this.headersSent = true;
  }

  get ended(): boolean {
    return this.done;
  }

  end(body?: string | Buffer): void {
    if (this.done) return;
    this.done = true;
    const payload = body === undefined ? Buffer.alloc(0) : typeof body === 'string' ? Buffer.from(body, 'utf8') : body;
    let head = `HTTP/1.1 ${this.status} ${HTTP_REASON[this.status] ?? ''}\r\n`;
    for (const [name, value] of Object.entries(this.headers)) head += `${name}: ${value}\r\n`;
    head += `connection: ${this.closeAfter ? 'close' : 'keep-alive'}\r\n\r\n`;
    // A HEAD answer carries the headers but no body.
    const bytes =
      this.method === 'HEAD' ? Buffer.from(head, 'ascii') : Buffer.concat([Buffer.from(head, 'ascii'), payload]);
    try {
      this.socket.write(bytes);
    } catch {
      // The socket is already gone; the answer has nowhere to go.
    }
    this.onFinished();
    if (this.closeAfter) {
      try {
        this.socket.end();
      } catch {
        // Already gone.
      }
    }
  }
}

/** One socket's parse state: the buffered bytes, the queued requests, the one in flight. */
interface SocketState {
  socket: Socket;
  buffer: Buffer;
  head: RequestHead | null;
  queue: ParsedRequest[];
  busy: boolean;
  currentRequest: ShimRequest | null;
  alive: boolean;
}

/** Start the next queued request on a socket, if one is waiting and none runs. */
function pumpSocket(state: SocketState): void {
  if (!state.alive || state.busy || state.queue.length === 0) return;
  state.busy = true;
  const next = state.queue.shift()!;
  void dispatchRequest(state, next);
}

/**
 * Run one request through the handlers. The response is always written
 * exactly once: by the handler, by the error path, or by the safety net
 * below when a handler returns without answering.
 */
async function dispatchRequest(state: SocketState, parsed: ParsedRequest): Promise<void> {
  let finished = false;
  const finish = (): void => {
    if (finished) return;
    finished = true;
    state.busy = false;
    // A microtask hop keeps a pipelined burst from nesting dispatch calls.
    queueMicrotask(() => pumpSocket(state));
  };
  const req = new ShimRequest(parsed.method, parsed.url, parsed.headers, parsed.body, state.socket);
  const res = new ShimResponse(state.socket, parsed.method, parsed.closeAfter, finish);
  state.currentRequest = req;
  try {
    await handleRequest(req as unknown as IncomingMessage, res as unknown as ServerResponse);
  } catch (err) {
    try {
      process.stderr.write(`[entry] request error: ${err instanceof Error ? err.stack ?? err.message : String(err)}\n`);
    } catch {
      // stderr is gone; nothing left to do
    }
    if (!res.headersSent) {
      try {
        sendError(res as unknown as ServerResponse, err instanceof HttpError ? err.status : 500, err instanceof Error ? err.message : 'Internal Server Error');
      } catch {
        // The socket is already gone.
      }
    } else {
      try {
        (res as unknown as ServerResponse).end();
      } catch {
        // The socket is already gone.
      }
    }
  } finally {
    state.currentRequest = null;
  }
  if (!res.ended) {
    try {
      if (!res.headersSent) sendError(res as unknown as ServerResponse, 500, 'Internal Server Error');
      else (res as unknown as ServerResponse).end();
    } catch {
      // The socket is already gone.
    }
  }
  finish();
}

export function createApp(): TcpServer {
  const server = createTcpServer((socket) => {
    socket.setNoDelay(true);
    const state: SocketState = {
      socket,
      buffer: Buffer.alloc(0),
      head: null,
      queue: [],
      busy: false,
      currentRequest: null,
      alive: true,
    };
    const teardown = (): void => {
      if (!state.alive) return;
      state.alive = false;
      state.queue.length = 0;
      if (state.currentRequest !== null) state.currentRequest.fail(new Error('socket closed'));
    };
    socket.on('error', teardown);
    socket.on('close', teardown);
    socket.on('data', (chunk: Buffer) => {
      if (!state.alive) return;
      state.buffer = state.buffer.length === 0 ? chunk : Buffer.concat([state.buffer, chunk]);
      try {
        for (;;) {
          if (state.head === null) {
            const head = parseHttpHead(state.buffer);
            if (head === null) break;
            state.buffer = state.buffer.subarray(head.headLength);
            state.head = head;
            if ((head.headers['expect'] ?? '').toLowerCase() === '100-continue') {
              socket.write('HTTP/1.1 100 Continue\r\n\r\n');
            }
          }
          const bodyResult = readHttpBody(state.head, state.buffer);
          if (bodyResult === null) break;
          state.buffer = state.buffer.subarray(bodyResult.consumed);
          state.queue.push({
            method: state.head.method,
            url: state.head.url,
            headers: state.head.headers,
            body: bodyResult.body,
            closeAfter: state.head.closeAfter,
          });
          state.head = null;
        }
      } catch {
        // Malformed wire: answer 400 and drop the connection.
        const badBody = Buffer.from('{"message":"malformed request"}\n', 'utf8');
        try {
          socket.write(
            Buffer.concat([
              Buffer.from(
                `HTTP/1.1 400 Bad Request\r\ncontent-type: application/json; charset=utf-8\r\ncontent-length: ${badBody.length}\r\nconnection: close\r\n\r\n`,
                'ascii',
              ),
              badBody,
            ]),
          );
        } catch {
          // The socket is already gone.
        }
        state.alive = false;
        try {
          socket.destroy();
        } catch {
          // Already gone.
        }
        return;
      }
      pumpSocket(state);
    });
  });
  return server;
}
