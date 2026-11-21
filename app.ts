// A GitHub-compatible git forge in one process: git smart HTTP, REST v3, GraphQL v4 and an MCP
// endpoint over a single in-memory store. Node stdlib only; git objects are stored and served by
// this file (no git binary). State is deterministic: ids come from counters and timestamps from a
// fixed epoch plus a counter, so a replayed trial exports byte-identical results.

import { createServer, type IncomingMessage, type Server, type ServerResponse } from 'node:http';
import { createHash } from 'node:crypto';
import { deflateSync, inflateSync } from 'node:zlib';

const JSON_TYPE = 'application/json; charset=utf-8';
const ZERO_OID = '0000000000000000000000000000000000000000';
const VIEWER_LOGIN = 'adaiversen';
const VIEWER_ID = 1000;
const VIEWER_NAME = 'ada iversen';
const TOKEN = process.env.MAKEFUN_SHOP_TOKEN ?? '';
const EPOCH_MS = 1_735_689_600_000; // 2025-01-01T00:00:00Z; every timestamp derives from this + a counter.
const DEFAULT_BRANCH = 'main';
const FORGE_IDENTITY = 'Forge Bot <forge@example.invalid>';

// ------------------------------------------------------------------ deterministic clock and ids

let clockTicks = 0;
function tickIso(): string {
  clockTicks += 1;
  return new Date(EPOCH_MS + clockTicks * 1000).toISOString();
}
function tickUnix(): number {
  clockTicks += 1;
  return Math.floor(EPOCH_MS / 1000) + clockTicks;
}

let requestSeq = 0;
function requestId(): string {
  requestSeq += 1;
  return `forge-${requestSeq.toString(36)}-${(requestSeq * 7919).toString(36)}`;
}

// ------------------------------------------------------------------ git object store

type ObjType = 'blob' | 'tree' | 'commit' | 'tag';
const OBJ_TYPE_CODE: Record<ObjType, number> = { commit: 1, tree: 2, blob: 3, tag: 4 };
const CODE_OBJ_TYPE: Record<number, ObjType> = { 1: 'commit', 2: 'tree', 3: 'blob', 4: 'tag' };

interface StoredObject {
  type: ObjType;
  data: Buffer;
}

const objectStore = new Map<string, StoredObject>();

function hashObject(type: ObjType, data: Buffer): string {
  const hash = createHash('sha1');
  hash.update(`${type} ${data.length}\0`, 'utf8');
  hash.update(data);
  return hash.digest('hex');
}

function putObject(type: ObjType, data: Buffer): string {
  const oid = hashObject(type, data);
  if (!objectStore.has(oid)) objectStore.set(oid, { type, data });
  return oid;
}

function getObject(oid: string): StoredObject | undefined {
  return objectStore.get(oid);
}

// ------------------------------------------------------------------ trees and commits

interface TreeEntry {
  mode: string;
  name: string;
  oid: string;
}

function isDirMode(mode: string): boolean {
  return mode === '40000' || mode === '040000' || mode === 'tree';
}

function parseTree(data: Buffer): TreeEntry[] {
  const entries: TreeEntry[] = [];
  let offset = 0;
  while (offset < data.length) {
    const space = data.indexOf(0x20, offset);
    if (space < 0) break;
    const mode = data.toString('utf8', offset, space);
    const nul = data.indexOf(0x00, space + 1);
    if (nul < 0 || nul + 21 > data.length) break;
    const name = data.toString('utf8', space + 1, nul);
    const oid = data.toString('hex', nul + 1, nul + 21);
    entries.push({ mode, name, oid });
    offset = nul + 21;
  }
  return entries;
}

function buildTreeData(entries: readonly TreeEntry[]): Buffer {
  const sorted = [...entries].sort((a, b) => {
    const ka = a.name + (isDirMode(a.mode) ? '/' : '');
    const kb = b.name + (isDirMode(b.mode) ? '/' : '');
    return ka < kb ? -1 : ka > kb ? 1 : 0;
  });
  const parts: Buffer[] = [];
  for (const entry of sorted) {
    parts.push(Buffer.from(`${entry.mode} ${entry.name}\0`, 'utf8'));
    parts.push(Buffer.from(entry.oid, 'hex'));
  }
  return Buffer.concat(parts);
}

function storeTree(entries: readonly TreeEntry[]): string {
  return putObject('tree', buildTreeData(entries));
}

const EMPTY_TREE_OID = storeTree([]);

interface CommitInfo {
  tree: string;
  parents: string[];
  message: string;
}

function parseCommit(data: Buffer): CommitInfo {
  const text = data.toString('utf8');
  const blank = text.indexOf('\n\n');
  const head = blank < 0 ? text : text.slice(0, blank);
  const message = blank < 0 ? '' : text.slice(blank + 2);
  let tree = '';
  const parents: string[] = [];
  for (const line of head.split('\n')) {
    if (line.startsWith('tree ')) tree = line.slice(5).trim();
    else if (line.startsWith('parent ')) parents.push(line.slice(7).trim());
  }
  return { tree, parents, message };
}

function makeCommit(tree: string, parents: readonly string[], message: string): string {
  const ts = tickUnix();
  const lines = [`tree ${tree}`];
  for (const parent of parents) lines.push(`parent ${parent}`);
  lines.push(`author ${FORGE_IDENTITY} ${ts} +0000`);
  lines.push(`committer ${FORGE_IDENTITY} ${ts} +0000`);
  lines.push('');
  lines.push(message.endsWith('\n') ? message.slice(0, -1) : message);
  return putObject('commit', Buffer.from(`${lines.join('\n')}\n`, 'utf8'));
}

/** Resolve any object id to the commit it points at (following tag objects), or null. */
function resolveToCommit(oid: string): string | null {
  let current = oid;
  for (let hops = 0; hops < 16; hops += 1) {
    const obj = getObject(current);
    if (obj === undefined) return null;
    if (obj.type === 'commit') return current;
    if (obj.type === 'tag') {
      const match = /^object ([0-9a-f]{40})$/m.exec(obj.data.toString('utf8'));
      if (match === null) return null;
      current = match[1]!;
      continue;
    }
    return null;
  }
  return null;
}

/** The root tree oid of a commit, or null. */
function commitTree(commitOid: string): string | null {
  const obj = getObject(commitOid);
  if (obj === undefined || obj.type !== 'commit') return null;
  return parseCommit(obj.data).tree;
}

/** Walk a tree by path parts; returns the entry found, or null. */
function treeLookup(rootTree: string | null, parts: readonly string[]): TreeEntry | null {
  if (rootTree === null || parts.length === 0) return null;
  let current = rootTree;
  for (let i = 0; i < parts.length; i += 1) {
    const obj = getObject(current);
    if (obj === undefined || obj.type !== 'tree') return null;
    const entry = parseTree(obj.data).find((e) => e.name === parts[i]);
    if (entry === undefined) return null;
    if (i === parts.length - 1) return entry;
    if (!isDirMode(entry.mode)) return null;
    current = entry.oid;
  }
  return null;
}

/** Return a new tree with `parts` set to the given blob oid (creating subtrees as needed). */
function treeSet(rootTree: string | null, parts: readonly string[], blobOid: string): string {
  const entries: TreeEntry[] = rootTree === null ? [] : parseTree(getObject(rootTree)?.data ?? Buffer.alloc(0));
  const [head, ...rest] = parts as [string, ...string[]];
  const existing = entries.find((e) => e.name === head);
  let replacement: TreeEntry;
  if (rest.length === 0) {
    replacement = { mode: '100644', name: head, oid: blobOid };
  } else {
    const subRoot = existing !== undefined && isDirMode(existing.mode) ? existing.oid : null;
    replacement = { mode: '40000', name: head, oid: treeSet(subRoot, rest, blobOid) };
  }
  const next = entries.filter((e) => e.name !== head);
  next.push(replacement);
  return storeTree(next);
}

/** Return a new tree with `parts` removed, or null when nothing is left at this level. */
function treeDelete(rootTree: string, parts: readonly string[]): string | null {
  const obj = getObject(rootTree);
  if (obj === undefined || obj.type !== 'tree') return rootTree;
  const entries = parseTree(obj.data);
  const [head, ...rest] = parts as [string, ...string[]];
  const existing = entries.find((e) => e.name === head);
  if (existing === undefined) return rootTree;
  let next: TreeEntry[];
  if (rest.length === 0) {
    next = entries.filter((e) => e.name !== head);
  } else {
    if (!isDirMode(existing.mode)) return rootTree;
    const sub = treeDelete(existing.oid, rest);
    next = entries.filter((e) => e.name !== head);
    if (sub !== null) next.push({ mode: '40000', name: head, oid: sub });
  }
  if (next.length === 0) return null;
  return storeTree(next);
}

/** Flatten a tree into a map of full path -> blob oid. */
function flattenTree(rootTree: string | null, prefix = '', out = new Map<string, string>()): Map<string, string> {
  if (rootTree === null) return out;
  const obj = getObject(rootTree);
  if (obj === undefined || obj.type !== 'tree') return out;
  for (const entry of parseTree(obj.data)) {
    const path = prefix === '' ? entry.name : `${prefix}/${entry.name}`;
    if (isDirMode(entry.mode)) flattenTree(entry.oid, path, out);
    else out.set(path, entry.oid);
  }
  return out;
}

/** Every object reachable from the given tips: the tips themselves (tag objects included), their targets, ancestors, trees and blobs. */
function reachableFromCommits(tips: readonly string[]): Set<string> {
  const seen = new Set<string>();
  const stack: string[] = [];
  for (const tip of tips) {
    if (getObject(tip) !== undefined) stack.push(tip);
  }
  while (stack.length > 0) {
    const oid = stack.pop()!;
    if (seen.has(oid)) continue;
    const obj = getObject(oid);
    if (obj === undefined) continue;
    seen.add(oid);
    if (obj.type === 'commit') {
      const info = parseCommit(obj.data);
      stack.push(info.tree);
      for (const parent of info.parents) stack.push(parent);
    } else if (obj.type === 'tree') {
      for (const entry of parseTree(obj.data)) stack.push(entry.oid);
    } else if (obj.type === 'tag') {
      const match = /^object ([0-9a-f]{40})$/m.exec(obj.data.toString('utf8'));
      if (match !== null) stack.push(match[1]!);
    }
  }
  return seen;
}

/** BFS depth of every commit reachable from the wants (want commits are depth 1). */
function commitDepths(wants: readonly string[]): Map<string, number> {
  const depths = new Map<string, number>();
  const queue: string[] = [];
  for (const want of wants) {
    const commit = resolveToCommit(want);
    if (commit !== null && !depths.has(commit)) {
      depths.set(commit, 1);
      queue.push(commit);
    }
  }
  while (queue.length > 0) {
    const oid = queue.shift()!;
    const depth = depths.get(oid)!;
    const obj = getObject(oid);
    if (obj === undefined || obj.type !== 'commit') continue;
    for (const parent of parseCommit(obj.data).parents) {
      if (!depths.has(parent)) {
        depths.set(parent, depth + 1);
        queue.push(parent);
      }
    }
  }
  return depths;
}

/** True when `ancestor` is `descendant` itself or one of its ancestors. */
function isAncestor(ancestor: string, descendant: string): boolean {
  const seen = new Set<string>();
  const stack = [descendant];
  while (stack.length > 0) {
    const oid = stack.pop()!;
    if (oid === ancestor) return true;
    if (seen.has(oid)) continue;
    seen.add(oid);
    const obj = getObject(oid);
    if (obj === undefined || obj.type !== 'commit') continue;
    for (const parent of parseCommit(obj.data).parents) stack.push(parent);
  }
  return false;
}

// ------------------------------------------------------------------ repository store

interface CommentRec {
  id: number;
  body: string;
}

interface IssueRec {
  id: number;
  number: number;
  title: string;
  body: string;
  state: 'open' | 'closed';
  labels: string[];
  comments: CommentRec[];
  nextCommentId: number;
}

interface PullRec {
  id: number;
  number: number;
  title: string;
  body: string;
  state: 'open' | 'closed';
  head: string;
  base: string;
  headSha: string;
  baseSha: string;
  merged: boolean;
  mergeSha: string | null;
  mergedAt: string | null;
}

interface RepoRec {
  id: number;
  name: string;
  description: string;
  priv: boolean;
  createdAt: string;
  refs: Map<string, string>;
  labels: Map<string, { name: string; color: string }>;
  issues: Map<number, IssueRec>;
  pulls: Map<number, PullRec>;
  nextNumber: number;
}

const repos = new Map<string, RepoRec>();
let nextRepoId = 1;
let nextIssueId = 1;

function createRepo(name: string, description: string, priv: boolean): RepoRec {
  const repo: RepoRec = {
    id: nextRepoId,
    name,
    description,
    priv,
    createdAt: tickIso(),
    refs: new Map(),
    labels: new Map(),
    issues: new Map(),
    pulls: new Map(),
    nextNumber: 1,
  };
  nextRepoId += 1;
  repos.set(name, repo);
  return repo;
}

function branchRef(branch: string): string {
  return `refs/heads/${branch}`;
}

function branchTip(repo: RepoRec, branch: string): string | null {
  return repo.refs.get(branchRef(branch)) ?? null;
}

function createIssue(repo: RepoRec, title: string, body: string, labels: readonly string[]): IssueRec {
  const issue: IssueRec = {
    id: nextIssueId,
    number: repo.nextNumber,
    title,
    body,
    state: 'open',
    labels: [...labels],
    comments: [],
    nextCommentId: 1,
  };
  nextIssueId += 1;
  repo.nextNumber += 1;
  repo.issues.set(issue.number, issue);
  return issue;
}

function createPull(repo: RepoRec, title: string, body: string, head: string, base: string): PullRec | null {
  const headSha = branchTip(repo, head);
  const baseSha = branchTip(repo, base);
  if (headSha === null || baseSha === null) return null;
  const pull: PullRec = {
    id: nextIssueId,
    number: repo.nextNumber,
    title,
    body,
    state: 'open',
    head,
    base,
    headSha,
    baseSha,
    merged: false,
    mergeSha: null,
    mergedAt: null,
  };
  nextIssueId += 1;
  repo.nextNumber += 1;
  repo.pulls.set(pull.number, pull);
  return pull;
}

/** Paths whose blob differs between two trees, as {path, before, after} (null = absent). */
function diffTrees(beforeTree: string | null, afterTree: string | null): Array<{ path: string; before: string | null; after: string | null }> {
  const before = flattenTree(beforeTree);
  const after = flattenTree(afterTree);
  const paths = new Set<string>([...before.keys(), ...after.keys()]);
  const out: Array<{ path: string; before: string | null; after: string | null }> = [];
  for (const path of [...paths].sort()) {
    const b = before.get(path) ?? null;
    const a = after.get(path) ?? null;
    if (b !== a) out.push({ path, before: b, after: a });
  }
  return out;
}

function lineCount(data: Buffer): number {
  if (data.length === 0) return 0;
  const text = data.toString('utf8');
  const lines = text.split('\n');
  return text.endsWith('\n') ? lines.length - 1 : lines.length;
}

/**
 * Three-way merge of a pull request against the current base tip. Returns the merged tree oid, or
 * null on conflict: a path the head changed relative to the PR's original base conflicts when the
 * current base's version differs from both the original base version and the head version.
 */
function mergePullTree(repo: RepoRec, pull: PullRec): string | null {
  const currentBaseTip = branchTip(repo, pull.base) ?? pull.baseSha;
  const headTip = branchTip(repo, pull.head) ?? pull.headSha;
  const original = flattenTree(commitTree(pull.baseSha));
  const current = flattenTree(commitTree(currentBaseTip));
  const head = flattenTree(commitTree(headTip));
  const paths = new Set<string>([...original.keys(), ...current.keys(), ...head.keys()]);
  const merged = new Map<string, string>();
  for (const path of paths) {
    const o = original.get(path) ?? null;
    const c = current.get(path) ?? null;
    const h = head.get(path) ?? null;
    let result: string | null;
    if (h === o) result = c;
    else if (c === o) result = h;
    else if (c === h) result = c;
    else return null;
    if (result !== null) merged.set(path, result);
  }
  // Rebuild a tree from the flat path map.
  let root: string | null = null;
  for (const [path, oid] of [...merged.entries()].sort()) {
    root = treeSet(root, path.split('/'), oid);
  }
  return root ?? EMPTY_TREE_OID;
}

/** Squash-merge a pull request onto its base branch. Returns the merge commit sha, or 'conflict'. */
function mergePull(repo: RepoRec, pull: PullRec): string | 'conflict' {
  if (pull.merged) return pull.mergeSha ?? 'conflict';
  const mergedTree = mergePullTree(repo, pull);
  if (mergedTree === null) return 'conflict';
  const currentBaseTip = branchTip(repo, pull.base) ?? pull.baseSha;
  const sha = makeCommit(mergedTree, [currentBaseTip], `${pull.title} (#${pull.number})\n`);
  repo.refs.set(branchRef(pull.base), sha);
  pull.state = 'closed';
  pull.merged = true;
  pull.mergeSha = sha;
  pull.mergedAt = tickIso();
  return sha;
}

// ------------------------------------------------------------------ HTTP plumbing

function sendJson(res: ServerResponse, status: number, body: unknown, headers: Readonly<Record<string, string>> = {}): void {
  const text = `${JSON.stringify(body)}\n`;
  res.writeHead(status, { 'content-type': JSON_TYPE, 'content-length': Buffer.byteLength(text), ...headers });
  res.end(text);
}

function sendApiJson(res: ServerResponse, status: number, body: unknown, headers: Readonly<Record<string, string>> = {}): void {
  sendJson(res, status, body, { 'x-github-request-id': requestId(), ...headers });
}

function apiError(res: ServerResponse, status: number, message: string): void {
  sendApiJson(res, status, { message });
}

function readBody(req: IncomingMessage): Promise<Buffer> {
  return new Promise((resolve, reject) => {
    const chunks: Buffer[] = [];
    let total = 0;
    req.on('data', (chunk: Buffer) => {
      total += chunk.length;
      if (total > 64 * 1024 * 1024) {
        reject(new Error('request body too large'));
        req.destroy();
        return;
      }
      chunks.push(chunk);
    });
    req.on('end', () => resolve(Buffer.concat(chunks)));
    req.on('error', reject);
  });
}

function authorized(req: IncomingMessage): boolean {
  const header = req.headers.authorization;
  if (typeof header !== 'string') return false;
  if (!header.startsWith('Bearer ')) return false;
  const presented = header.slice('Bearer '.length);
  if (TOKEN !== '') return presented === TOKEN;
  return presented.length > 0;
}

function parseJsonBody(raw: Buffer): { ok: true; value: unknown } | { ok: false } {
  try {
    return { ok: true, value: JSON.parse(raw.toString('utf8')) };
  } catch {
    return { ok: false };
  }
}

function isRecord(value: unknown): value is Record<string, unknown> {
  return value !== null && typeof value === 'object' && !Array.isArray(value);
}

function str(value: unknown): string {
  return typeof value === 'string' ? value : '';
}

// ------------------------------------------------------------------ REST JSON shapes

function repoJson(repo: RepoRec): Record<string, unknown> {
  return {
    id: repo.id,
    node_id: `R_${repo.id}`,
    name: repo.name,
    full_name: `${VIEWER_LOGIN}/${repo.name}`,
    owner: { login: VIEWER_LOGIN, id: VIEWER_ID, type: 'User' },
    private: repo.priv,
    description: repo.description,
    default_branch: DEFAULT_BRANCH,
    has_issues: true,
    has_projects: false,
    has_wiki: false,
    created_at: repo.createdAt,
    updated_at: repo.createdAt,
    pushed_at: repo.createdAt,
    html_url: `https://forge.invalid/${VIEWER_LOGIN}/${repo.name}`,
    url: `/api/v3/repos/${VIEWER_LOGIN}/${repo.name}`,
    size: 0,
    stargazers_count: 0,
    watchers_count: 0,
    forks_count: 0,
    open_issues_count: [...repo.issues.values()].filter((i) => i.state === 'open').length,
  };
}

function labelJson(label: { name: string; color: string }): Record<string, unknown> {
  return { name: label.name, color: label.color, description: null, default: false };
}

function issueJson(repo: RepoRec, issue: IssueRec): Record<string, unknown> {
  return {
    id: issue.id,
    node_id: `I_${repo.id}_${issue.number}`,
    number: issue.number,
    title: issue.title,
    body: issue.body,
    state: issue.state,
    labels: issue.labels.map((name) => labelJson(repo.labels.get(name) ?? { name, color: '000000' })),
    user: { login: VIEWER_LOGIN, id: VIEWER_ID, type: 'User' },
    author: { login: VIEWER_LOGIN, id: VIEWER_ID },
    comments: issue.comments.length,
    created_at: repo.createdAt,
    updated_at: repo.createdAt,
    html_url: `https://forge.invalid/${VIEWER_LOGIN}/${repo.name}/issues/${issue.number}`,
    url: `/api/v3/repos/${VIEWER_LOGIN}/${repo.name}/issues/${issue.number}`,
  };
}

function pullJson(repo: RepoRec, pull: PullRec): Record<string, unknown> {
  const headSha = branchTip(repo, pull.head) ?? pull.headSha;
  const baseSha = branchTip(repo, pull.base) ?? pull.baseSha;
  return {
    id: pull.id,
    node_id: `PR_${repo.id}_${pull.number}`,
    number: pull.number,
    title: pull.title,
    body: pull.body,
    state: pull.state,
    merged: pull.merged,
    merged_at: pull.mergedAt,
    merge_commit_sha: pull.mergeSha,
    head: { ref: pull.head, sha: headSha, label: `${VIEWER_LOGIN}:${pull.head}` },
    base: { ref: pull.base, sha: baseSha, label: `${VIEWER_LOGIN}:${pull.base}` },
    user: { login: VIEWER_LOGIN, id: VIEWER_ID, type: 'User' },
    created_at: repo.createdAt,
    updated_at: repo.createdAt,
    html_url: `https://forge.invalid/${VIEWER_LOGIN}/${repo.name}/pull/${pull.number}`,
    url: `/api/v3/repos/${VIEWER_LOGIN}/${repo.name}/pulls/${pull.number}`,
  };
}

function commentJson(repo: RepoRec, issue: IssueRec, comment: CommentRec): Record<string, unknown> {
  return {
    id: comment.id,
    node_id: `C_${repo.id}_${issue.number}_${comment.id}`,
    body: comment.body,
    user: { login: VIEWER_LOGIN, id: VIEWER_ID, type: 'User' },
    author: { login: VIEWER_LOGIN, id: VIEWER_ID },
    created_at: repo.createdAt,
    updated_at: repo.createdAt,
    html_url: `https://forge.invalid/${VIEWER_LOGIN}/${repo.name}/issues/${issue.number}#issuecomment-${comment.id}`,
  };
}

/** Paginate a list the way the suite follows: per_page/page plus a Link rel="next" header. */
function paginate<T>(req: IncomingMessage, res: ServerResponse, url: URL, items: readonly T[]): T[] {
  const perPageRaw = Number(url.searchParams.get('per_page') ?? '30');
  const pageRaw = Number(url.searchParams.get('page') ?? '1');
  const perPage = Number.isFinite(perPageRaw) && perPageRaw > 0 ? Math.min(100, Math.trunc(perPageRaw)) : 30;
  const page = Number.isFinite(pageRaw) && pageRaw > 0 ? Math.trunc(pageRaw) : 1;
  const start = (page - 1) * perPage;
  const slice = items.slice(start, start + perPage);
  if (start + perPage < items.length) {
    const host = req.headers.host ?? 'forge.invalid';
    const next = new URL(url.pathname, `http://${host}`);
    next.searchParams.set('per_page', String(perPage));
    next.searchParams.set('page', String(page + 1));
    res.setHeader('link', `<${next.toString()}>; rel="next"`);
  }
  return slice;
}

// ------------------------------------------------------------------ REST handlers

function findRepo(res: ServerResponse, owner: string, name: string): RepoRec | null {
  if (owner !== VIEWER_LOGIN) {
    apiError(res, 404, 'Not Found');
    return null;
  }
  const repo = repos.get(name);
  if (repo === undefined) {
    apiError(res, 404, 'Not Found');
    return null;
  }
  return repo;
}

async function handleRest(req: IncomingMessage, res: ServerResponse, url: URL): Promise<void> {
  if (!authorized(req)) {
    apiError(res, 401, 'Requires authentication');
    return;
  }
  const method = req.method ?? 'GET';
  const segments = url.pathname.split('/').filter((s) => s !== '').slice(2); // after /api/v3
  const rawBody = method === 'GET' || method === 'HEAD' ? Buffer.alloc(0) : await readBody(req);
  let body: Record<string, unknown> = {};
  if (rawBody.length > 0 && (method === 'POST' || method === 'PUT' || method === 'PATCH' || method === 'DELETE')) {
    const parsed = parseJsonBody(rawBody);
    if (!parsed.ok) {
      apiError(res, 400, 'Problems parsing JSON');
      return;
    }
    if (isRecord(parsed.value)) body = parsed.value;
  }

  // Root and meta.
  if (segments.length === 0) {
    if (method === 'GET') {
      sendApiJson(res, 200, { current_user_url: '/api/v3/user', rate_limit_url: '/api/v3/rate_limit' }, { 'x-oauth-scopes': 'repo, read:org' });
      return;
    }
    apiError(res, 404, 'Not Found');
    return;
  }
  if (segments[0] === 'meta' && segments.length === 1 && method === 'GET') {
    sendApiJson(res, 200, { installed_version: '1.0.0', installed_version_major: 1 });
    return;
  }
  if (segments[0] === 'user' && segments.length === 1 && method === 'GET') {
    sendApiJson(res, 200, { login: VIEWER_LOGIN, id: VIEWER_ID, name: VIEWER_NAME, type: 'User' });
    return;
  }

  // The viewer's repositories.
  if (segments[0] === 'user' && segments[1] === 'repos' && segments.length === 2) {
    if (method === 'GET') {
      const all = [...repos.values()].sort((a, b) => a.id - b.id).map(repoJson);
      sendApiJson(res, 200, paginate(req, res, url, all));
      return;
    }
    if (method === 'POST') {
      const name = str(body.name);
      if (name === '') {
        apiError(res, 422, 'name is required');
        return;
      }
      if (repos.has(name)) {
        apiError(res, 422, 'name already exists on this account');
        return;
      }
      const repo = createRepo(name, str(body.description), body.private === true);
      sendApiJson(res, 201, repoJson(repo));
      return;
    }
  }

  if (segments[0] !== 'repos' || segments.length < 3) {
    apiError(res, 404, 'Not Found');
    return;
  }
  const owner = decodeURIComponent(segments[1]!);
  const repoName = decodeURIComponent(segments[2]!);
  const rest = segments.slice(3);
  const repo = findRepo(res, owner, repoName);
  if (repo === null) return;

  // Repository CRUD.
  if (rest.length === 0) {
    if (method === 'GET') {
      sendApiJson(res, 200, repoJson(repo));
      return;
    }
    if (method === 'PATCH') {
      if (typeof body.description === 'string') repo.description = body.description;
      if (typeof body.private === 'boolean') repo.priv = body.private;
      if (typeof body.name === 'string' && body.name !== '' && body.name !== repo.name && !repos.has(body.name)) {
        repos.delete(repo.name);
        repo.name = body.name;
        repos.set(repo.name, repo);
      }
      sendApiJson(res, 200, repoJson(repo));
      return;
    }
    if (method === 'DELETE') {
      repos.delete(repo.name);
      res.writeHead(204, { 'x-github-request-id': requestId() });
      res.end();
      return;
    }
    apiError(res, 404, 'Not Found');
    return;
  }

  // Contents API, backed by the git object store.
  if (rest[0] === 'contents') {
    const pathParts = rest.slice(1).map((s) => decodeURIComponent(s));
    handleContents(req, res, url, repo, method, pathParts, body);
    return;
  }

  // Git data: refs and branches.
  if (rest[0] === 'git' && rest[1] === 'refs' && rest.length === 2 && method === 'POST') {
    const ref = str(body.ref);
    const sha = str(body.sha);
    if (!/^refs\/(heads|tags)\//.test(ref) || getObject(sha) === undefined) {
      apiError(res, 422, 'Invalid ref or object');
      return;
    }
    repo.refs.set(ref, sha);
    sendApiJson(res, 201, { ref, object: { sha, type: getObject(sha)!.type } });
    return;
  }
  if (rest[0] === 'git' && rest[1] === 'refs' && rest[2] === 'heads' && rest.length === 4 && method === 'GET') {
    const branch = decodeURIComponent(rest[3]!);
    const tip = branchTip(repo, branch);
    if (tip === null) {
      apiError(res, 404, 'Not Found');
      return;
    }
    sendApiJson(res, 200, { ref: branchRef(branch), object: { sha: tip, type: 'commit' } });
    return;
  }
  if (rest[0] === 'branches' && rest.length === 1 && method === 'GET') {
    const out = [...repo.refs.entries()]
      .filter(([ref]) => ref.startsWith('refs/heads/'))
      .map(([ref, sha]) => ({ name: ref.slice('refs/heads/'.length), commit: { sha }, protected: false }));
    out.sort((a, b) => (a.name < b.name ? -1 : 1));
    sendApiJson(res, 200, out);
    return;
  }
  if (rest[0] === 'branches' && rest.length === 2 && method === 'GET') {
    const branch = decodeURIComponent(rest[1]!);
    const tip = branchTip(repo, branch);
    if (tip === null) {
      apiError(res, 404, 'Not Found');
      return;
    }
    sendApiJson(res, 200, { name: branch, commit: { sha: tip }, protected: false });
    return;
  }

  // Commit list, newest first from the requested tip.
  if (rest[0] === 'commits' && rest.length === 1 && method === 'GET') {
    const shaParam = url.searchParams.get('sha');
    let tip: string | null;
    if (shaParam === null || shaParam === '') tip = branchTip(repo, DEFAULT_BRANCH);
    else if (repo.refs.has(branchRef(shaParam))) tip = branchTip(repo, shaParam);
    else tip = resolveToCommit(shaParam);
    if (tip === null) {
      sendApiJson(res, 200, []);
      return;
    }
    const out: Array<Record<string, unknown>> = [];
    const seen = new Set<string>();
    const stack = [tip];
    const ordered: string[] = [];
    while (stack.length > 0 && ordered.length < 1000) {
      const oid = stack.pop()!;
      if (seen.has(oid)) continue;
      seen.add(oid);
      ordered.push(oid);
      const obj = getObject(oid);
      if (obj !== undefined && obj.type === 'commit') {
        const parents = parseCommit(obj.data).parents;
        for (let i = parents.length - 1; i >= 0; i -= 1) stack.push(parents[i]!);
      }
    }
    for (const oid of ordered) {
      const obj = getObject(oid);
      if (obj === undefined || obj.type !== 'commit') continue;
      const info = parseCommit(obj.data);
      out.push({
        sha: oid,
        commit: { message: info.message.replace(/\n+$/, ''), tree: { sha: info.tree } },
        parents: info.parents.map((p) => ({ sha: p })),
      });
    }
    sendApiJson(res, 200, out);
    return;
  }

  // Labels.
  if (rest[0] === 'labels') {
    if (rest.length === 1 && method === 'POST') {
      const name = str(body.name);
      if (name === '') {
        apiError(res, 422, 'name is required');
        return;
      }
      if (repo.labels.has(name)) {
        apiError(res, 422, 'Label already exists');
        return;
      }
      const label = { name, color: str(body.color) || '000000' };
      repo.labels.set(name, label);
      sendApiJson(res, 201, labelJson(label));
      return;
    }
    if (rest.length === 1 && method === 'GET') {
      sendApiJson(res, 200, [...repo.labels.values()].map(labelJson));
      return;
    }
    apiError(res, 404, 'Not Found');
    return;
  }

  // Issues and comments.
  if (rest[0] === 'issues') {
    if (rest.length === 1 && method === 'POST') {
      const labelNames: string[] = [];
      if (Array.isArray(body.labels)) {
        for (const entry of body.labels) {
          if (typeof entry === 'string') labelNames.push(entry);
          else if (isRecord(entry) && typeof entry.name === 'string') labelNames.push(entry.name);
        }
      }
      for (const name of labelNames) {
        if (!repo.labels.has(name)) {
          apiError(res, 422, `Label "${name}" does not exist`);
          return;
        }
      }
      const issue = createIssue(repo, str(body.title), str(body.body), labelNames);
      sendApiJson(res, 201, issueJson(repo, issue));
      return;
    }
    if (rest.length === 1 && method === 'GET') {
      const state = url.searchParams.get('state') ?? 'open';
      let list = [...repo.issues.values()];
      if (state === 'open') list = list.filter((i) => i.state === 'open');
      else if (state === 'closed') list = list.filter((i) => i.state === 'closed');
      const direction = url.searchParams.get('direction') ?? 'desc';
      list.sort((a, b) => (direction === 'asc' ? a.number - b.number : b.number - a.number));
      sendApiJson(res, 200, paginate(req, res, url, list.map((i) => issueJson(repo, i))));
      return;
    }
    if (rest.length >= 2) {
      const number = Number(rest[1]);
      const issue = Number.isInteger(number) ? repo.issues.get(number) : undefined;
      if (issue === undefined) {
        apiError(res, 404, 'Not Found');
        return;
      }
      if (rest.length === 2 && method === 'GET') {
        sendApiJson(res, 200, issueJson(repo, issue));
        return;
      }
      if (rest.length === 2 && method === 'PATCH') {
        if (body.state === 'closed' || body.state === 'open') issue.state = body.state;
        if (typeof body.title === 'string') issue.title = body.title;
        if (typeof body.body === 'string') issue.body = body.body;
        sendApiJson(res, 200, issueJson(repo, issue));
        return;
      }
      if (rest.length === 3 && rest[2] === 'comments' && method === 'POST') {
        const comment: CommentRec = { id: issue.nextCommentId, body: str(body.body) };
        issue.nextCommentId += 1;
        issue.comments.push(comment);
        sendApiJson(res, 201, commentJson(repo, issue, comment));
        return;
      }
      if (rest.length === 3 && rest[2] === 'comments' && method === 'GET') {
        sendApiJson(res, 200, issue.comments.map((c) => commentJson(repo, issue, c)));
        return;
      }
    }
    apiError(res, 404, 'Not Found');
    return;
  }

  // Pull requests.
  if (rest[0] === 'pulls') {
    if (rest.length === 1 && method === 'POST') {
      const pull = createPull(repo, str(body.title), str(body.body), str(body.head), str(body.base));
      if (pull === null) {
        apiError(res, 422, 'Invalid head or base branch');
        return;
      }
      sendApiJson(res, 201, pullJson(repo, pull));
      return;
    }
    if (rest.length === 1 && method === 'GET') {
      const state = url.searchParams.get('state') ?? 'open';
      let list = [...repo.pulls.values()];
      if (state === 'open') list = list.filter((p) => p.state === 'open');
      else if (state === 'closed') list = list.filter((p) => p.state === 'closed');
      list.sort((a, b) => b.number - a.number);
      sendApiJson(res, 200, paginate(req, res, url, list.map((p) => pullJson(repo, p))));
      return;
    }
    if (rest.length >= 2) {
      const number = Number(rest[1]);
      const pull = Number.isInteger(number) ? repo.pulls.get(number) : undefined;
      if (pull === undefined) {
        apiError(res, 404, 'Not Found');
        return;
      }
      if (rest.length === 2 && method === 'GET') {
        sendApiJson(res, 200, pullJson(repo, pull));
        return;
      }
      if (rest.length === 3 && rest[2] === 'files' && method === 'GET') {
        const baseTree = commitTree(pull.baseSha);
        const headTree = commitTree(branchTip(repo, pull.head) ?? pull.headSha);
        const files = diffTrees(baseTree, headTree).map((d) => {
          const beforeData = d.before === null ? null : (getObject(d.before)?.data ?? null);
          const afterData = d.after === null ? null : (getObject(d.after)?.data ?? null);
          const additions = afterData === null ? 0 : lineCount(afterData);
          const deletions = beforeData === null ? 0 : lineCount(beforeData);
          return {
            filename: d.path,
            status: d.before === null ? 'added' : d.after === null ? 'removed' : 'modified',
            additions,
            deletions,
            changes: additions + deletions,
            sha: d.after ?? d.before ?? '',
          };
        });
        sendApiJson(res, 200, files);
        return;
      }
      if (rest.length === 3 && rest[2] === 'merge' && method === 'PUT') {
        if (pull.merged) {
          apiError(res, 405, 'Pull Request is not mergeable');
          return;
        }
        const result = mergePull(repo, pull);
        if (result === 'conflict') {
          apiError(res, 405, 'Pull Request is not mergeable');
          return;
        }
        sendApiJson(res, 200, { sha: result, merged: true, message: 'Pull Request successfully merged' });
        return;
      }
    }
    apiError(res, 404, 'Not Found');
    return;
  }

  apiError(res, 404, 'Not Found');
}

/** The contents API: files and directories backed by the same git trees the smart-HTTP side serves. */
function handleContents(req: IncomingMessage, res: ServerResponse, url: URL, repo: RepoRec, method: string, pathParts: string[], body: Record<string, unknown>): void {
  const refParam = url.searchParams.get('ref');
  const resolveTree = (branch: string): string | null => {
    const tip = branchTip(repo, branch);
    return tip === null ? null : commitTree(tip);
  };

  if (method === 'GET') {
    let tip: string | null;
    if (refParam !== null && refParam !== '') {
      if (repo.refs.has(branchRef(refParam))) tip = branchTip(repo, refParam);
      else tip = resolveToCommit(refParam);
    } else {
      tip = branchTip(repo, DEFAULT_BRANCH);
    }
    if (tip === null) {
      apiError(res, 404, 'Not Found');
      return;
    }
    const rootTree = commitTree(tip);
    if (pathParts.length === 0 || (pathParts.length === 1 && pathParts[0] === '')) {
      const entries = rootTree === null ? [] : parseTree(getObject(rootTree)?.data ?? Buffer.alloc(0));
      sendApiJson(res, 200, entries.map((e) => ({
        type: isDirMode(e.mode) ? 'dir' : 'file',
        name: e.name,
        path: e.name,
        sha: e.oid,
      })));
      return;
    }
    const entry = treeLookup(rootTree, pathParts);
    if (entry === null) {
      apiError(res, 404, 'Not Found');
      return;
    }
    const path = pathParts.join('/');
    if (isDirMode(entry.mode)) {
      const entries = parseTree(getObject(entry.oid)?.data ?? Buffer.alloc(0));
      sendApiJson(res, 200, entries.map((e) => ({
        type: isDirMode(e.mode) ? 'dir' : 'file',
        name: e.name,
        path: `${path}/${e.name}`,
        sha: e.oid,
      })));
      return;
    }
    const blob = getObject(entry.oid);
    if (blob === undefined) {
      apiError(res, 404, 'Not Found');
      return;
    }
    sendApiJson(res, 200, {
      type: 'file',
      name: pathParts[pathParts.length - 1],
      path,
      sha: entry.oid,
      size: blob.data.length,
      encoding: 'base64',
      content: blob.data.toString('base64'),
    });
    return;
  }

  if (method === 'PUT') {
    if (pathParts.length === 0) {
      apiError(res, 422, 'path is required');
      return;
    }
    const branch = typeof body.branch === 'string' && body.branch !== '' ? body.branch : DEFAULT_BRANCH;
    const content = typeof body.content === 'string' ? Buffer.from(body.content, 'base64') : Buffer.alloc(0);
    const message = str(body.message) || 'Update file';
    let tip = branchTip(repo, branch);
    if (tip === null && branch !== DEFAULT_BRANCH) {
      // A contents write to a new branch starts it from the default branch's tip.
      const baseTip = branchTip(repo, DEFAULT_BRANCH);
      if (baseTip !== null) {
        repo.refs.set(branchRef(branch), baseTip);
        tip = baseTip;
      }
    }
    const rootTree = tip === null ? null : commitTree(tip);
    const existing = treeLookup(rootTree, pathParts);
    if (existing !== null && !isDirMode(existing.mode) && typeof body.sha === 'string' && body.sha !== existing.oid) {
      apiError(res, 409, 'SHA does not match');
      return;
    }
    const blobOid = putObject('blob', content);
    const newTree = treeSet(rootTree, pathParts, blobOid);
    const commitSha = makeCommit(newTree, tip === null ? [] : [tip], message);
    repo.refs.set(branchRef(branch), commitSha);
    sendApiJson(res, existing === null ? 201 : 200, {
      content: {
        name: pathParts[pathParts.length - 1],
        path: pathParts.join('/'),
        sha: blobOid,
        size: content.length,
        type: 'file',
        encoding: 'base64',
        content: content.toString('base64'),
      },
      commit: { sha: commitSha, message },
    });
    return;
  }

  if (method === 'DELETE') {
    const branch = typeof body.branch === 'string' && body.branch !== '' ? body.branch : DEFAULT_BRANCH;
    const tip = branchTip(repo, branch);
    if (tip === null) {
      apiError(res, 404, 'Not Found');
      return;
    }
    const rootTree = commitTree(tip);
    const existing = treeLookup(rootTree, pathParts);
    if (existing === null || isDirMode(existing.mode)) {
      apiError(res, 404, 'Not Found');
      return;
    }
    if (typeof body.sha === 'string' && body.sha !== existing.oid) {
      apiError(res, 409, 'SHA does not match');
      return;
    }
    const newTree = treeDelete(rootTree!, pathParts);
    const commitSha = makeCommit(newTree ?? EMPTY_TREE_OID, [tip], str(body.message) || 'Delete file');
    repo.refs.set(branchRef(branch), commitSha);
    sendApiJson(res, 200, { content: null, commit: { sha: commitSha, message: str(body.message) || 'Delete file' } });
    return;
  }

  apiError(res, 404, 'Not Found');
}

// ------------------------------------------------------------------ MCP endpoint

const MCP_SERVER_INFO = { name: 'makefun-forge', version: '1.0.0' };
const MCP_SUPPORTED_VERSIONS = ['2026-07-28', '2025-11-25', '2025-06-18', '2025-03-26'];

/** The tools/list answer, built once so two calls return byte-identical JSON. */
const MCP_TOOLS = [
  {
    name: 'create_repo',
    description: 'Create a repository owned by the authenticated user.',
    inputSchema: {
      type: 'object',
      properties: {
        name: { type: 'string', description: 'Repository name' },
        description: { type: 'string', description: 'Repository description' },
        private: { type: 'boolean', description: 'Whether the repository is private' },
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
        owner: { type: 'string', description: 'Repository owner login' },
        repo: { type: 'string', description: 'Repository name' },
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
        owner: { type: 'string', description: 'Repository owner login' },
        repo: { type: 'string', description: 'Repository name' },
        title: { type: 'string', description: 'Issue title' },
        body: { type: 'string', description: 'Issue body' },
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
        owner: { type: 'string', description: 'Repository owner login' },
        repo: { type: 'string', description: 'Repository name' },
        state: { type: 'string', description: 'Filter by state: open, closed or all' },
      },
      required: ['owner', 'repo'],
    },
  },
  {
    name: 'create_pull_request',
    description: 'Create a pull request between two branches of a repository.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'Repository owner login' },
        repo: { type: 'string', description: 'Repository name' },
        title: { type: 'string', description: 'Pull request title' },
        body: { type: 'string', description: 'Pull request body' },
        head: { type: 'string', description: 'Head branch name' },
        base: { type: 'string', description: 'Base branch name' },
      },
      required: ['owner', 'repo', 'title', 'head', 'base'],
    },
  },
  {
    name: 'merge_pull_request',
    description: 'Merge a pull request (squash) into its base branch.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'Repository owner login' },
        repo: { type: 'string', description: 'Repository name' },
        pull_number: { type: 'number', description: 'Pull request number' },
      },
      required: ['owner', 'repo', 'pull_number'],
    },
  },
];

function mcpToolOk(value: unknown): Record<string, unknown> {
  return { content: [{ type: 'text', text: JSON.stringify(value) }], structuredContent: value, isError: false };
}

function mcpToolFail(message: string): Record<string, unknown> {
  return { content: [{ type: 'text', text: message }], isError: true };
}

function mcpRepo(args: Record<string, unknown>): RepoRec | null {
  const owner = args.owner;
  const name = args.repo;
  if (typeof owner !== 'string' || typeof name !== 'string') return null;
  if (owner !== VIEWER_LOGIN) return null;
  return repos.get(name) ?? null;
}

function callMcpTool(name: string, args: Record<string, unknown>): Record<string, unknown> | 'unknown' {
  switch (name) {
    case 'create_repo': {
      const repoName = args.name;
      if (typeof repoName !== 'string' || repoName === '') return mcpToolFail('missing required argument: name');
      const existing = repos.get(repoName);
      if (existing !== undefined) return mcpToolOk(repoJson(existing));
      const repo = createRepo(repoName, typeof args.description === 'string' ? args.description : '', args.private === true);
      return mcpToolOk(repoJson(repo));
    }
    case 'get_repo': {
      if (typeof args.owner !== 'string' || typeof args.repo !== 'string') return mcpToolFail('missing required argument: owner/repo');
      const repo = mcpRepo(args);
      if (repo === null) return mcpToolFail('repository not found');
      return mcpToolOk(repoJson(repo));
    }
    case 'create_issue': {
      if (typeof args.owner !== 'string' || typeof args.repo !== 'string' || typeof args.title !== 'string') {
        return mcpToolFail('missing required argument: owner/repo/title');
      }
      const repo = mcpRepo(args);
      if (repo === null) return mcpToolFail('repository not found');
      const issue = createIssue(repo, args.title, typeof args.body === 'string' ? args.body : '', []);
      return mcpToolOk(issueJson(repo, issue));
    }
    case 'list_issues': {
      if (typeof args.owner !== 'string' || typeof args.repo !== 'string') return mcpToolFail('missing required argument: owner/repo');
      const repo = mcpRepo(args);
      if (repo === null) return mcpToolFail('repository not found');
      let list = [...repo.issues.values()].sort((a, b) => a.number - b.number);
      if (args.state === 'open') list = list.filter((i) => i.state === 'open');
      else if (args.state === 'closed') list = list.filter((i) => i.state === 'closed');
      const issues = list.map((i) => issueJson(repo, i));
      return mcpToolOk({ issues, total_count: issues.length });
    }
    case 'create_pull_request': {
      if (
        typeof args.owner !== 'string' || typeof args.repo !== 'string' || typeof args.title !== 'string' ||
        typeof args.head !== 'string' || typeof args.base !== 'string'
      ) {
        return mcpToolFail('missing required argument: owner/repo/title/head/base');
      }
      const repo = mcpRepo(args);
      if (repo === null) return mcpToolFail('repository not found');
      const pull = createPull(repo, args.title, typeof args.body === 'string' ? args.body : '', args.head, args.base);
      if (pull === null) return mcpToolFail('invalid head or base branch');
      return mcpToolOk(pullJson(repo, pull));
    }
    case 'merge_pull_request': {
      if (typeof args.owner !== 'string' || typeof args.repo !== 'string' || (typeof args.pull_number !== 'number' && typeof args.pull_number !== 'string')) {
        return mcpToolFail('missing required argument: owner/repo/pull_number');
      }
      const repo = mcpRepo(args);
      if (repo === null) return mcpToolFail('repository not found');
      const pull = repo.pulls.get(Number(args.pull_number));
      if (pull === undefined) return mcpToolFail('pull request not found');
      const result = mergePull(repo, pull);
      if (result === 'conflict') return mcpToolFail('pull request is not mergeable');
      return mcpToolOk(pullJson(repo, pull));
    }
    default:
      return 'unknown';
  }
}

function mcpDispatch(message: Record<string, unknown>): Record<string, unknown> | null {
  const id = message.id;
  const method = typeof message.method === 'string' ? message.method : '';
  const params = isRecord(message.params) ? message.params : {};
  const result = (value: unknown): Record<string, unknown> => ({ jsonrpc: '2.0', id: id ?? null, result: value });
  const failure = (code: number, text: string): Record<string, unknown> => ({ jsonrpc: '2.0', id: id ?? null, error: { code, message: text } });

  if (method === 'server/discover') {
    return result({ supportedVersions: MCP_SUPPORTED_VERSIONS, capabilities: { tools: {} }, serverInfo: MCP_SERVER_INFO });
  }
  if (method === 'initialize') {
    const requested = typeof params.protocolVersion === 'string' ? params.protocolVersion : '2025-11-25';
    return result({ protocolVersion: requested, capabilities: { tools: {} }, serverInfo: MCP_SERVER_INFO });
  }
  if (method === 'ping') return result({});
  if (method === 'tools/list') return result({ tools: MCP_TOOLS });
  if (method === 'tools/call') {
    const toolName = typeof params.name === 'string' ? params.name : '';
    const args = isRecord(params.arguments) ? params.arguments : {};
    const outcome = callMcpTool(toolName, args);
    if (outcome === 'unknown') return failure(-32602, `unknown tool: ${toolName}`);
    return result(outcome);
  }
  if (method.startsWith('notifications/')) return null;
  return failure(-32601, `method not found: ${method}`);
}

async function handleMcp(req: IncomingMessage, res: ServerResponse): Promise<void> {
  const method = req.method ?? 'GET';
  if (method === 'DELETE') {
    sendJson(res, 200, {});
    return;
  }
  if (method !== 'POST') {
    sendJson(res, 405, { jsonrpc: '2.0', id: null, error: { code: -32601, message: 'method not allowed' } });
    return;
  }
  if (!authorized(req)) {
    sendJson(res, 401, { message: 'Requires authentication' });
    return;
  }
  const raw = await readBody(req);
  const text = raw.toString('utf8');
  let parsed: unknown;
  try {
    parsed = JSON.parse(text);
  } catch {
    const idMatch = /"id"\s*:\s*("(?:[^"\\]|\\.)*"|-?\d+)/.exec(text);
    let id: unknown = null;
    if (idMatch !== null) {
      try {
        id = JSON.parse(idMatch[1]!);
      } catch {
        id = null;
      }
    }
    sendJson(res, 400, { jsonrpc: '2.0', id, error: { code: -32700, message: 'Parse error' } });
    return;
  }
  if (Array.isArray(parsed)) {
    const answers: Array<Record<string, unknown>> = [];
    for (const entry of parsed) {
      if (!isRecord(entry)) continue;
      const answer = mcpDispatch(entry);
      if (answer !== null) answers.push(answer);
    }
    sendJson(res, 200, answers);
    return;
  }
  if (!isRecord(parsed)) {
    sendJson(res, 400, { jsonrpc: '2.0', id: null, error: { code: -32600, message: 'Invalid request' } });
    return;
  }
  if (!('id' in parsed)) {
    // A notification: accepted, no answer body.
    res.writeHead(202);
    res.end();
    return;
  }
  const answer = mcpDispatch(parsed);
  if (answer === null) {
    res.writeHead(202);
    res.end();
    return;
  }
  sendJson(res, 200, answer);
}

// ------------------------------------------------------------------ git smart HTTP

function pktLine(payload: Buffer | string): Buffer {
  const data = typeof payload === 'string' ? Buffer.from(payload, 'utf8') : payload;
  const head = (data.length + 4).toString(16).padStart(4, '0');
  return Buffer.concat([Buffer.from(head, 'ascii'), data]);
}

const PKT_FLUSH = Buffer.from('0000', 'ascii');

interface PktItem {
  kind: 'data' | 'flush' | 'delim' | 'end';
  data: Buffer;
}

/** Parse pkt-lines from `start`; stops after a flush/end packet. Null when the framing is malformed. */
function parsePktLines(buf: Buffer, start = 0): { items: PktItem[]; end: number } | null {
  const items: PktItem[] = [];
  let offset = start;
  while (offset + 4 <= buf.length) {
    const hex = buf.toString('ascii', offset, offset + 4);
    if (!/^[0-9a-fA-F]{4}$/.test(hex)) return null;
    const len = Number.parseInt(hex, 16);
    if (len === 0) {
      items.push({ kind: 'flush', data: Buffer.alloc(0) });
      return { items, end: offset + 4 };
    }
    if (len === 1) {
      items.push({ kind: 'delim', data: Buffer.alloc(0) });
      offset += 4;
      continue;
    }
    if (len === 2) {
      items.push({ kind: 'end', data: Buffer.alloc(0) });
      return { items, end: offset + 4 };
    }
    if (len < 4 || offset + len > buf.length) return null;
    items.push({ kind: 'data', data: buf.subarray(offset + 4, offset + len) });
    offset += len;
  }
  return { items, end: offset };
}

function pktText(item: PktItem): string {
  return item.data.toString('utf8').replace(/\n$/, '');
}

/** Split a v2 command request into the lines before the delim (command + capabilities) and the args after it. */
function splitCommand(items: readonly PktItem[]): { head: string[]; args: string[] } {
  const head: string[] = [];
  const args: string[] = [];
  let inArgs = false;
  for (const item of items) {
    if (item.kind === 'delim') {
      inArgs = true;
      continue;
    }
    if (item.kind !== 'data') break;
    (inArgs ? args : head).push(pktText(item));
  }
  return { head, args };
}

/** Inflate the zlib stream starting at `offset`; returns the data and the offset just past the stream. */
function inflateExact(buf: Buffer, offset: number): { data: Buffer; next: number } {
  let lo = 1;
  let hi = buf.length - offset;
  let found = -1;
  let result: Buffer | null = null;
  while (lo <= hi) {
    const mid = (lo + hi) >> 1;
    try {
      result = inflateSync(buf.subarray(offset, offset + mid));
      found = mid;
      hi = mid - 1;
    } catch {
      lo = mid + 1;
    }
  }
  if (found < 0 || result === null) throw new Error('corrupt zlib stream in pack');
  return { data: result, next: offset + found };
}

function applyDelta(base: Buffer, delta: Buffer): Buffer {
  let offset = 0;
  const readVarint = (): number => {
    let value = 0;
    let shift = 0;
    for (;;) {
      const byte = delta[offset]!;
      offset += 1;
      value |= (byte & 0x7f) << shift;
      shift += 7;
      if ((byte & 0x80) === 0) break;
    }
    return value;
  };
  const sourceSize = readVarint();
  const targetSize = readVarint();
  if (sourceSize !== base.length) throw new Error('delta base size mismatch');
  const parts: Buffer[] = [];
  while (offset < delta.length) {
    const cmd = delta[offset]!;
    offset += 1;
    if ((cmd & 0x80) !== 0) {
      let cpOff = 0;
      let cpSize = 0;
      if ((cmd & 0x01) !== 0) cpOff = delta[offset++]!;
      if ((cmd & 0x02) !== 0) cpOff |= delta[offset++]! << 8;
      if ((cmd & 0x04) !== 0) cpOff |= delta[offset++]! << 16;
      if ((cmd & 0x08) !== 0) cpOff |= delta[offset++]! << 24;
      if ((cmd & 0x10) !== 0) cpSize = delta[offset++]!;
      if ((cmd & 0x20) !== 0) cpSize |= delta[offset++]! << 8;
      if ((cmd & 0x40) !== 0) cpSize |= delta[offset++]! << 16;
      if (cpSize === 0) cpSize = 0x10000;
      parts.push(base.subarray(cpOff, cpOff + cpSize));
    } else if (cmd !== 0) {
      parts.push(delta.subarray(offset, offset + cmd));
      offset += cmd;
    } else {
      throw new Error('bad delta opcode');
    }
  }
  const out = Buffer.concat(parts);
  if (out.length !== targetSize) throw new Error('delta target size mismatch');
  return out;
}

/** Parse a packfile into the objects it carries, resolving OFS/REF deltas. Throws on malformed input. */
function parsePack(pack: Buffer): Map<string, StoredObject> {
  if (pack.length < 12 || pack.toString('ascii', 0, 4) !== 'PACK') throw new Error('bad pack header');
  const count = pack.readUInt32BE(8);
  let offset = 12;
  const byPosition = new Map<number, StoredObject>();
  const resolved = new Map<string, StoredObject>();
  const pending: Array<{ start: number; baseOid: string | null; basePos: number | null; delta: Buffer }> = [];
  for (let i = 0; i < count; i += 1) {
    const start = offset;
    let byte = pack[offset]!;
    offset += 1;
    const typeCode = (byte >> 4) & 7;
    let size = byte & 0x0f;
    let shift = 4;
    while ((byte & 0x80) !== 0) {
      byte = pack[offset]!;
      offset += 1;
      size |= (byte & 0x7f) << shift;
      shift += 7;
    }
    let baseOid: string | null = null;
    let basePos: number | null = null;
    if (typeCode === 6) {
      byte = pack[offset]!;
      offset += 1;
      let back = byte & 0x7f;
      while ((byte & 0x80) !== 0) {
        byte = pack[offset]!;
        offset += 1;
        back = ((back + 1) << 7) | (byte & 0x7f);
      }
      basePos = start - back;
    } else if (typeCode === 7) {
      baseOid = pack.toString('hex', offset, offset + 20);
      offset += 20;
    }
    const inflated = inflateExact(pack, offset);
    offset = inflated.next;
    if (typeCode === 6 || typeCode === 7) {
      pending.push({ start, baseOid, basePos, delta: inflated.data });
    } else {
      const type = CODE_OBJ_TYPE[typeCode];
      if (type === undefined) throw new Error(`unknown pack object type ${typeCode}`);
      const obj: StoredObject = { type, data: inflated.data };
      byPosition.set(start, obj);
      resolved.set(hashObject(type, inflated.data), obj);
    }
  }
  let remaining = pending;
  for (let guard = 0; remaining.length > 0 && guard < 64; guard += 1) {
    const stuck: typeof remaining = [];
    for (const entry of remaining) {
      let base: StoredObject | undefined;
      if (entry.basePos !== null) base = byPosition.get(entry.basePos);
      else if (entry.baseOid !== null) base = resolved.get(entry.baseOid) ?? getObject(entry.baseOid);
      if (base === undefined) {
        stuck.push(entry);
        continue;
      }
      const data = applyDelta(base.data, entry.delta);
      const obj: StoredObject = { type: base.type, data };
      byPosition.set(entry.start, obj);
      resolved.set(hashObject(base.type, data), obj);
    }
    if (stuck.length === remaining.length) throw new Error('unresolvable pack delta');
    remaining = stuck;
  }
  if (remaining.length > 0) throw new Error('unresolvable pack delta');
  return resolved;
}

/** Build a packfile (no deltas) from object ids, in the order given. */
function buildPack(oids: readonly string[]): Buffer {
  const present = oids.filter((oid) => getObject(oid) !== undefined);
  const header = Buffer.alloc(12);
  header.write('PACK', 0, 'ascii');
  header.writeUInt32BE(2, 4);
  header.writeUInt32BE(present.length, 8);
  const parts: Buffer[] = [header];
  for (const oid of present) {
    const obj = getObject(oid)!;
    const size = obj.data.length;
    const headBytes: number[] = [];
    let first = (OBJ_TYPE_CODE[obj.type] << 4) | (size & 0x0f);
    let rest = size >> 4;
    if (rest > 0) first |= 0x80;
    headBytes.push(first);
    while (rest > 0) {
      let byte = rest & 0x7f;
      rest >>= 7;
      if (rest > 0) byte |= 0x80;
      headBytes.push(byte);
    }
    parts.push(Buffer.from(headBytes));
    parts.push(deflateSync(obj.data));
  }
  const body = Buffer.concat(parts);
  const trailer = createHash('sha1').update(body).digest();
  return Buffer.concat([body, trailer]);
}

/** Frame pack bytes as sideband-64k packets (band 1), each within the pkt-line size limit. */
function sidebandPackets(pack: Buffer): Buffer[] {
  const out: Buffer[] = [];
  const CHUNK = 65515;
  for (let offset = 0; offset < pack.length; offset += CHUNK) {
    const chunk = pack.subarray(offset, Math.min(pack.length, offset + CHUNK));
    out.push(pktLine(Buffer.concat([Buffer.from([1]), chunk])));
  }
  if (out.length === 0) out.push(pktLine(Buffer.from([1])));
  return out;
}

function refsAdvertisement(repo: RepoRec, capabilities: string): Buffer {
  const names = [...repo.refs.keys()].sort();
  if (names.length === 0) {
    return pktLine(`${ZERO_OID} capabilities^{}\0${capabilities}`);
  }
  const lines: Array<{ oid: string; name: string }> = [];
  const headTip = repo.refs.get(branchRef(DEFAULT_BRANCH));
  if (headTip !== undefined) lines.push({ oid: headTip, name: 'HEAD' });
  for (const name of names) lines.push({ oid: repo.refs.get(name)!, name });
  const parts: Buffer[] = [];
  lines.forEach((line, index) => {
    const suffix = index === 0 ? `\0${capabilities}` : '';
    parts.push(pktLine(`${line.oid} ${line.name}${suffix}`));
    if (line.name.startsWith('refs/tags/')) {
      const obj = getObject(line.oid);
      if (obj !== undefined && obj.type === 'tag') {
        const commit = resolveToCommit(line.oid);
        if (commit !== null && commit !== line.oid) parts.push(pktLine(`${commit} ${line.name}^{}`));
      }
    }
  });
  return Buffer.concat(parts);
}

const UPLOAD_CAPS_V0 = 'side-band-64k shallow thin-pack ofs-delta symref=HEAD:refs/heads/main agent=forge/1.0';
const RECEIVE_CAPS = 'report-status side-band-64k delete-refs ofs-delta agent=forge/1.0';

function handleLsRefs(repo: RepoRec, args: readonly string[]): Buffer {
  const prefixes = args.filter((a) => a.startsWith('ref-prefix ')).map((a) => a.slice('ref-prefix '.length));
  const wantPeel = args.includes('peel');
  const wantSymrefs = args.includes('symrefs');
  const wantUnborn = args.includes('unborn');
  const matches = (name: string): boolean => prefixes.length === 0 || prefixes.some((p) => name.startsWith(p));
  const lines: string[] = [];
  const headTip = repo.refs.get(branchRef(DEFAULT_BRANCH)) ?? null;
  if (matches('HEAD')) {
    if (headTip !== null) {
      lines.push(`${headTip} HEAD${wantSymrefs ? ` symref-target:${branchRef(DEFAULT_BRANCH)}` : ''}`);
    } else if (wantUnborn) {
      lines.push(`unborn HEAD symref-target:${branchRef(DEFAULT_BRANCH)}`);
    }
  }
  for (const name of [...repo.refs.keys()].sort()) {
    if (!matches(name)) continue;
    const oid = repo.refs.get(name)!;
    let line = `${oid} ${name}`;
    if (wantPeel) {
      const obj = getObject(oid);
      if (obj !== undefined && obj.type === 'tag') {
        const commit = resolveToCommit(oid);
        if (commit !== null && commit !== oid) line += ` peeled:${commit}`;
      }
    }
    lines.push(line);
  }
  return Buffer.concat([...lines.map((l) => pktLine(`${l}\n`)), PKT_FLUSH]);
}

/** Objects of the given commits plus their full tree/blob closure (no ancestors). */
function closureOfCommits(commitOids: readonly string[]): Set<string> {
  const seen = new Set<string>();
  const stack: string[] = [];
  for (const commit of commitOids) {
    if (getObject(commit) === undefined) continue;
    seen.add(commit);
    const tree = commitTree(commit);
    if (tree !== null) stack.push(tree);
  }
  while (stack.length > 0) {
    const oid = stack.pop()!;
    if (seen.has(oid)) continue;
    const obj = getObject(oid);
    if (obj === undefined) continue;
    seen.add(oid);
    if (obj.type === 'tree') {
      for (const entry of parseTree(obj.data)) stack.push(entry.oid);
    }
  }
  return seen;
}

/** Order a delivery set deterministically: commits by depth, then trees, blobs, tags by id. */
function orderDelivery(oids: Set<string>, depths: Map<string, number>): string[] {
  const commits: string[] = [];
  const trees: string[] = [];
  const blobs: string[] = [];
  const tags: string[] = [];
  for (const oid of oids) {
    const obj = getObject(oid);
    if (obj === undefined) continue;
    if (obj.type === 'commit') commits.push(oid);
    else if (obj.type === 'tree') trees.push(oid);
    else if (obj.type === 'blob') blobs.push(oid);
    else tags.push(oid);
  }
  commits.sort((a, b) => (depths.get(a) ?? 0) - (depths.get(b) ?? 0) || (a < b ? -1 : 1));
  trees.sort();
  blobs.sort();
  tags.sort();
  return [...commits, ...trees, ...blobs, ...tags];
}

function fetchSection(name: string, lines: readonly string[]): Buffer {
  return Buffer.concat([pktLine(`${name}\n`), ...lines.map((l) => pktLine(l)), PKT_FLUSH]);
}

function handleFetchV2(repo: RepoRec, args: readonly string[]): Buffer {
  const wants: string[] = [];
  const haves: string[] = [];
  const shallowIn: string[] = [];
  let deepen: number | null = null;
  let done = false;
  for (const arg of args) {
    if (arg.startsWith('want ')) wants.push(arg.slice(5).trim());
    else if (arg.startsWith('have ')) haves.push(arg.slice(5).trim());
    else if (arg.startsWith('shallow ')) shallowIn.push(arg.slice(8).trim());
    else if (arg.startsWith('deepen ')) deepen = Number.parseInt(arg.slice(7), 10);
    else if (arg === 'done') done = true;
  }
  if (!done) {
    const common = haves.filter((h) => getObject(h) !== undefined);
    const lines = common.length > 0 ? common.map((h) => `ACK ${h}\n`) : ['NAK\n'];
    return fetchSection('acknowledgments', lines);
  }
  const haveSet = reachableFromCommits(haves);
  const depths = commitDepths(wants);
  let deliver: Set<string>;
  let shallowOut: string[] = [];
  let unshallowOut: string[] = [];
  if (deepen !== null && Number.isFinite(deepen)) {
    // `deepen N` is an absolute depth measured from the wants. What the client already holds is the
    // closure of the commits it names as shallow boundary or haves — never their full ancestry.
    const limit = deepen;
    const included: string[] = [];
    for (const [commit, depth] of depths) {
      if (depth <= limit) included.push(commit);
    }
    const heldCommits: string[] = [];
    for (const oid of [...shallowIn, ...haves]) {
      const commit = resolveToCommit(oid);
      if (commit !== null && !heldCommits.includes(commit)) heldCommits.push(commit);
    }
    deliver = closureOfCommits(included);
    for (const oid of closureOfCommits(heldCommits)) deliver.delete(oid);
    shallowOut = included.filter((c) => depths.get(c) === limit && (getObject(c)?.type === 'commit' && parseCommit(getObject(c)!.data).parents.length > 0));
    if (shallowIn.length > 0) {
      unshallowOut = shallowIn.filter((o) => (depths.get(o) ?? Number.POSITIVE_INFINITY) < limit);
    }
    // The wants themselves may be tags or other objects: include them directly.
    for (const want of wants) if (getObject(want) !== undefined) deliver.add(want);
  } else {
    deliver = reachableFromCommits(wants);
    for (const oid of haveSet) deliver.delete(oid);
  }
  const pack = buildPack(orderDelivery(deliver, depths));
  const parts: Buffer[] = [fetchSection('acknowledgments', ['ready\n'])];
  if (shallowOut.length > 0 || unshallowOut.length > 0) {
    parts.push(fetchSection('shallow-info', [
      ...shallowOut.map((o) => `shallow ${o}\n`),
      ...unshallowOut.map((o) => `unshallow ${o}\n`),
    ]));
  }
  parts.push(pktLine('packfile\n'));
  parts.push(...sidebandPackets(pack));
  parts.push(PKT_FLUSH);
  return Buffer.concat(parts);
}

function handleFetchV0(repo: RepoRec, raw: Buffer): Buffer | null {
  const first = parsePktLines(raw, 0);
  if (first === null) return null;
  const wants: string[] = [];
  for (const item of first.items) {
    if (item.kind !== 'data') continue;
    const line = pktText(item);
    if (line.startsWith('want ')) wants.push(line.slice(5, 45));
  }
  const rest = parsePktLines(raw, first.end);
  const haves: string[] = [];
  if (rest !== null) {
    for (const item of rest.items) {
      if (item.kind !== 'data') continue;
      const line = pktText(item);
      if (line.startsWith('have ')) haves.push(line.slice(5, 45));
    }
  }
  const deliver = reachableFromCommits(wants);
  for (const oid of reachableFromCommits(haves)) deliver.delete(oid);
  const pack = buildPack(orderDelivery(deliver, new Map()));
  return Buffer.concat([pktLine('NAK\n'), ...sidebandPackets(pack), PKT_FLUSH]);
}

async function handleReceivePack(res: ServerResponse, repo: RepoRec, raw: Buffer): Promise<void> {
  const parsed = parsePktLines(raw, 0);
  if (parsed === null) {
    res.writeHead(400, { 'content-type': 'text/plain' });
    res.end('malformed pkt-line stream');
    return;
  }
  interface Command {
    oldOid: string;
    newOid: string;
    ref: string;
  }
  const commands: Command[] = [];
  let capabilities = '';
  for (const item of parsed.items) {
    if (item.kind !== 'data') continue;
    let line = pktText(item);
    const nul = line.indexOf('\0');
    if (nul >= 0) {
      capabilities = line.slice(nul + 1);
      line = line.slice(0, nul);
    }
    const fields = line.split(' ');
    if (fields.length >= 3) commands.push({ oldOid: fields[0]!, newOid: fields[1]!, ref: fields[2]! });
  }
  const pack = raw.subarray(parsed.end);
  let unpackOk = true;
  if (pack.length > 0) {
    try {
      const objects = parsePack(pack);
      for (const [oid, obj] of objects) {
        if (!objectStore.has(oid)) objectStore.set(oid, obj);
      }
    } catch {
      unpackOk = false;
    }
  }
  const results: Array<{ ref: string; ok: boolean; reason: string }> = [];
  for (const command of commands) {
    if (!unpackOk) {
      results.push({ ref: command.ref, ok: false, reason: 'unpacker error' });
      continue;
    }
    if (command.newOid === ZERO_OID) {
      if (repo.refs.has(command.ref)) {
        repo.refs.delete(command.ref);
        results.push({ ref: command.ref, ok: true, reason: '' });
      } else {
        results.push({ ref: command.ref, ok: false, reason: 'reference not found' });
      }
      continue;
    }
    if (getObject(command.newOid) === undefined) {
      results.push({ ref: command.ref, ok: false, reason: 'invalid object' });
      continue;
    }
    const current = repo.refs.get(command.ref) ?? ZERO_OID;
    if (current === ZERO_OID || current === command.newOid || command.ref.startsWith('refs/tags/')) {
      repo.refs.set(command.ref, command.newOid);
      results.push({ ref: command.ref, ok: true, reason: '' });
      continue;
    }
    const newCommit = resolveToCommit(command.newOid);
    if (newCommit !== null && isAncestor(current, newCommit)) {
      repo.refs.set(command.ref, command.newOid);
      results.push({ ref: command.ref, ok: true, reason: '' });
    } else {
      results.push({ ref: command.ref, ok: false, reason: 'non-fast-forward' });
    }
  }
  const reportLines = [
    `unpack ${unpackOk ? 'ok' : 'error'}\n`,
    ...results.map((r) => (r.ok ? `ok ${r.ref}\n` : `ng ${r.ref} ${r.reason}\n`)),
  ];
  const reportPkts = [...reportLines.map((l) => pktLine(l)), PKT_FLUSH];
  let body: Buffer;
  if (capabilities.split(' ').includes('side-band-64k')) {
    body = Buffer.concat([
      ...reportPkts.slice(0, -1).map((p) => pktLine(Buffer.concat([Buffer.from([1]), p]))),
      PKT_FLUSH,
    ]);
  } else {
    body = Buffer.concat(reportPkts);
  }
  res.writeHead(200, { 'content-type': 'application/x-git-receive-pack-result' });
  res.end(body);
}

async function handleGitHttp(req: IncomingMessage, res: ServerResponse, url: URL): Promise<void> {
  const match = /^\/([^/]+)\/([^/]+)\.git\/(info\/refs|git-upload-pack|git-receive-pack)$/.exec(url.pathname);
  if (match === null) {
    sendJson(res, 404, { message: 'Not Found' });
    return;
  }
  if (!authorized(req)) {
    sendJson(res, 401, { message: 'Requires authentication' });
    return;
  }
  const owner = decodeURIComponent(match[1]!);
  const name = decodeURIComponent(match[2]!);
  const endpoint = match[3]!;
  const repo = owner === VIEWER_LOGIN ? repos.get(name) : undefined;
  if (repo === undefined) {
    sendJson(res, 404, { message: 'Not Found' });
    return;
  }
  const method = req.method ?? 'GET';

  if (endpoint === 'info/refs' && method === 'GET') {
    const service = url.searchParams.get('service');
    if (service === 'git-upload-pack') {
      const protocol = req.headers['git-protocol'];
      if (typeof protocol === 'string' && protocol.includes('version=2')) {
        const body = Buffer.concat([
          pktLine('version 2\n'),
          pktLine('agent=forge/1.0\n'),
          pktLine('ls-refs=unborn\n'),
          pktLine('fetch=shallow thin-pack ofs-delta no-progress\n'),
          pktLine('object-format=sha1\n'),
          PKT_FLUSH,
        ]);
        res.writeHead(200, { 'content-type': 'application/x-git-upload-pack-advertisement' });
        res.end(body);
        return;
      }
      const body = Buffer.concat([
        pktLine('# service=git-upload-pack\n'),
        PKT_FLUSH,
        refsAdvertisement(repo, UPLOAD_CAPS_V0),
        PKT_FLUSH,
      ]);
      res.writeHead(200, { 'content-type': 'application/x-git-upload-pack-advertisement' });
      res.end(body);
      return;
    }
    if (service === 'git-receive-pack') {
      const body = Buffer.concat([
        pktLine('# service=git-receive-pack\n'),
        PKT_FLUSH,
        refsAdvertisement(repo, RECEIVE_CAPS),
        PKT_FLUSH,
      ]);
      res.writeHead(200, { 'content-type': 'application/x-git-receive-pack-advertisement' });
      res.end(body);
      return;
    }
    res.writeHead(400, { 'content-type': 'text/plain' });
    res.end('missing or unknown service');
    return;
  }

  if (endpoint === 'git-upload-pack' && method === 'POST') {
    const raw = await readBody(req);
    const parsed = parsePktLines(raw, 0);
    if (parsed === null || parsed.items.length === 0 || parsed.items[0]!.kind !== 'data') {
      res.writeHead(400, { 'content-type': 'text/plain' });
      res.end('malformed pkt-line stream');
      return;
    }
    const firstLine = pktText(parsed.items[0]!);
    if (firstLine.startsWith('command=ls-refs')) {
      const { args } = splitCommand(parsed.items);
      res.writeHead(200, { 'content-type': 'application/x-git-upload-pack-result' });
      res.end(handleLsRefs(repo, args));
      return;
    }
    if (firstLine.startsWith('command=fetch')) {
      const { args } = splitCommand(parsed.items);
      res.writeHead(200, { 'content-type': 'application/x-git-upload-pack-result' });
      res.end(handleFetchV2(repo, args));
      return;
    }
    if (firstLine.startsWith('want ')) {
      const body = handleFetchV0(repo, raw);
      if (body === null) {
        res.writeHead(400, { 'content-type': 'text/plain' });
        res.end('malformed pkt-line stream');
        return;
      }
      res.writeHead(200, { 'content-type': 'application/x-git-upload-pack-result' });
      res.end(body);
      return;
    }
    res.writeHead(400, { 'content-type': 'text/plain' });
    res.end('unknown upload-pack command');
    return;
  }

  if (endpoint === 'git-receive-pack' && method === 'POST') {
    const raw = await readBody(req);
    await handleReceivePack(res, repo, raw);
    return;
  }

  sendJson(res, 404, { message: 'Not Found' });
}

// ------------------------------------------------------------------ GraphQL: parser

type GqlValue =
  | { kind: 'variable'; name: string }
  | { kind: 'string'; value: string }
  | { kind: 'number'; value: number }
  | { kind: 'boolean'; value: boolean }
  | { kind: 'null' }
  | { kind: 'enum'; value: string }
  | { kind: 'list'; values: GqlValue[] }
  | { kind: 'object'; fields: Map<string, GqlValue> };

interface GqlFieldNode {
  name: string;
  alias?: string;
  args: Map<string, GqlValue>;
  selection?: GqlSelection[];
}

type GqlSelection =
  | { kind: 'field'; field: GqlFieldNode }
  | { kind: 'inline'; typeCondition?: string; selection: GqlSelection[] }
  | { kind: 'spread'; name: string };

interface GqlOperationNode {
  type: 'query' | 'mutation';
  name?: string;
  selection: GqlSelection[];
}

interface GqlDocument {
  operations: GqlOperationNode[];
  fragments: Map<string, { typeCondition: string; selection: GqlSelection[] }>;
}

interface GqlToken {
  kind: 'name' | 'string' | 'number' | 'punct' | 'eof';
  value: string;
}

function gqlTokenize(source: string): GqlToken[] {
  const tokens: GqlToken[] = [];
  let i = 0;
  while (i < source.length) {
    const ch = source[i]!;
    if (ch === ' ' || ch === '\t' || ch === '\n' || ch === '\r' || ch === ',' || ch === '﻿') {
      i += 1;
      continue;
    }
    if (ch === '#') {
      while (i < source.length && source[i] !== '\n') i += 1;
      continue;
    }
    if (source.startsWith('...', i)) {
      tokens.push({ kind: 'punct', value: '...' });
      i += 3;
      continue;
    }
    if ('{}()[]:=@$!|&'.includes(ch)) {
      tokens.push({ kind: 'punct', value: ch });
      i += 1;
      continue;
    }
    if (ch === '"') {
      if (source.startsWith('"""', i)) {
        const end = source.indexOf('"""', i + 3);
        const text = end < 0 ? source.slice(i + 3) : source.slice(i + 3, end);
        tokens.push({ kind: 'string', value: text });
        i = end < 0 ? source.length : end + 3;
        continue;
      }
      let j = i + 1;
      let text = '';
      while (j < source.length && source[j] !== '"') {
        if (source[j] === '\\' && j + 1 < source.length) {
          const esc = source[j + 1]!;
          if (esc === 'n') text += '\n';
          else if (esc === 't') text += '\t';
          else if (esc === 'r') text += '\r';
          else if (esc === 'b') text += '\b';
          else if (esc === 'f') text += '\f';
          else if (esc === 'u') {
            text += String.fromCharCode(Number.parseInt(source.slice(j + 2, j + 6), 16));
            j += 4;
          } else text += esc;
          j += 2;
        } else {
          text += source[j];
          j += 1;
        }
      }
      tokens.push({ kind: 'string', value: text });
      i = j + 1;
      continue;
    }
    if (/[0-9-]/.test(ch)) {
      let j = i;
      while (j < source.length && /[0-9.eE+-]/.test(source[j]!)) j += 1;
      tokens.push({ kind: 'number', value: source.slice(i, j) });
      i = j;
      continue;
    }
    if (/[_A-Za-z]/.test(ch)) {
      let j = i;
      while (j < source.length && /[_0-9A-Za-z]/.test(source[j]!)) j += 1;
      tokens.push({ kind: 'name', value: source.slice(i, j) });
      i = j;
      continue;
    }
    i += 1;
  }
  tokens.push({ kind: 'eof', value: '' });
  return tokens;
}

class GqlParser {
  private tokens: GqlToken[];
  private pos = 0;

  constructor(source: string) {
    this.tokens = gqlTokenize(source);
  }

  private peek(): GqlToken {
    return this.tokens[this.pos]!;
  }

  private next(): GqlToken {
    const token = this.tokens[this.pos]!;
    this.pos += 1;
    return token;
  }

  private expectPunct(value: string): void {
    const token = this.next();
    if (token.kind !== 'punct' || token.value !== value) throw new Error(`expected "${value}", got "${token.value}"`);
  }

  private atPunct(value: string): boolean {
    const token = this.peek();
    return token.kind === 'punct' && token.value === value;
  }

  parseDocument(): GqlDocument {
    const operations: GqlOperationNode[] = [];
    const fragments = new Map<string, { typeCondition: string; selection: GqlSelection[] }>();
    while (this.peek().kind !== 'eof') {
      const token = this.peek();
      if (token.kind === 'punct' && token.value === '{') {
        operations.push({ type: 'query', selection: this.parseSelectionSet() });
        continue;
      }
      if (token.kind === 'name' && (token.value === 'query' || token.value === 'mutation' || token.value === 'subscription')) {
        this.next();
        let name: string | undefined;
        if (this.peek().kind === 'name') name = this.next().value;
        if (this.atPunct('(')) this.skipBalancedParens();
        this.skipDirectives();
        const selection = this.parseSelectionSet();
        operations.push({ type: token.value === 'mutation' ? 'mutation' : 'query', name, selection });
        continue;
      }
      if (token.kind === 'name' && token.value === 'fragment') {
        this.next();
        const fragName = this.next().value;
        this.next(); // 'on'
        const typeCondition = this.next().value;
        this.skipDirectives();
        const selection = this.parseSelectionSet();
        fragments.set(fragName, { typeCondition, selection });
        continue;
      }
      throw new Error(`unexpected token "${token.value}" in document`);
    }
    return { operations, fragments };
  }

  private skipBalancedParens(): void {
    let depth = 0;
    do {
      const token = this.next();
      if (token.kind === 'eof') throw new Error('unbalanced parentheses');
      if (token.kind === 'punct' && token.value === '(') depth += 1;
      if (token.kind === 'punct' && token.value === ')') depth -= 1;
    } while (depth > 0);
  }

  private skipDirectives(): void {
    while (this.atPunct('@')) {
      this.next();
      this.next(); // directive name
      if (this.atPunct('(')) this.skipBalancedParens();
    }
  }

  private parseSelectionSet(): GqlSelection[] {
    this.expectPunct('{');
    const selections: GqlSelection[] = [];
    while (!this.atPunct('}')) {
      if (this.peek().kind === 'eof') throw new Error('unterminated selection set');
      if (this.atPunct('...')) {
        this.next();
        const token = this.peek();
        if (token.kind === 'name' && token.value === 'on') {
          this.next();
          const typeCondition = this.next().value;
          this.skipDirectives();
          selections.push({ kind: 'inline', typeCondition, selection: this.parseSelectionSet() });
        } else if (token.kind === 'name') {
          const name = this.next().value;
          this.skipDirectives();
          selections.push({ kind: 'spread', name });
        } else {
          throw new Error('bad fragment selection');
        }
        continue;
      }
      selections.push({ kind: 'field', field: this.parseField() });
    }
    this.expectPunct('}');
    return selections;
  }

  private parseField(): GqlFieldNode {
    const first = this.next();
    if (first.kind !== 'name') throw new Error(`expected a field name, got "${first.value}"`);
    let name = first.value;
    let alias: string | undefined;
    if (this.atPunct(':')) {
      this.next();
      alias = name;
      name = this.next().value;
    }
    const args = new Map<string, GqlValue>();
    if (this.atPunct('(')) {
      this.next();
      while (!this.atPunct(')')) {
        const argName = this.next().value;
        this.expectPunct(':');
        args.set(argName, this.parseValue());
      }
      this.expectPunct(')');
    }
    this.skipDirectives();
    let selection: GqlSelection[] | undefined;
    if (this.atPunct('{')) selection = this.parseSelectionSet();
    return { name, alias, args, selection };
  }

  private parseValue(): GqlValue {
    const token = this.next();
    if (token.kind === 'punct' && token.value === '$') {
      return { kind: 'variable', name: this.next().value };
    }
    if (token.kind === 'string') return { kind: 'string', value: token.value };
    if (token.kind === 'number') return { kind: 'number', value: Number(token.value) };
    if (token.kind === 'name') {
      if (token.value === 'true') return { kind: 'boolean', value: true };
      if (token.value === 'false') return { kind: 'boolean', value: false };
      if (token.value === 'null') return { kind: 'null' };
      return { kind: 'enum', value: token.value };
    }
    if (token.kind === 'punct' && token.value === '[') {
      const values: GqlValue[] = [];
      while (!this.atPunct(']')) values.push(this.parseValue());
      this.expectPunct(']');
      return { kind: 'list', values };
    }
    if (token.kind === 'punct' && token.value === '{') {
      const fields = new Map<string, GqlValue>();
      while (!this.atPunct('}')) {
        const key = this.next().value;
        this.expectPunct(':');
        fields.set(key, this.parseValue());
      }
      this.expectPunct('}');
      return { kind: 'object', fields };
    }
    throw new Error(`unexpected value token "${token.value}"`);
  }
}

function gqlValue(value: GqlValue, vars: Record<string, unknown>): unknown {
  switch (value.kind) {
    case 'variable':
      return vars[value.name] ?? null;
    case 'string':
    case 'enum':
      return value.value;
    case 'number':
    case 'boolean':
      return value.value;
    case 'null':
      return null;
    case 'list':
      return value.values.map((v) => gqlValue(v, vars));
    case 'object': {
      const out: Record<string, unknown> = {};
      for (const [key, entry] of value.fields) out[key] = gqlValue(entry, vars);
      return out;
    }
  }
}

// ------------------------------------------------------------------ GraphQL: schema and execution

const TYPE_FIELDS: Record<string, string[]> = {
  Query: ['viewer', 'repository', 'node', '__type', '__schema'],
  Mutation: ['createIssue', 'closeIssue', 'createPullRequest', 'mergePullRequest', 'addComment'],
  User: ['login', 'id', 'databaseId', 'name', 'email', 'url'],
  Node: ['id'],
  Repository: [
    'id', 'databaseId', 'name', 'nameWithOwner', 'owner', 'defaultBranchRef', 'viewerPermission',
    'hasIssuesEnabled', 'issue', 'issues', 'pullRequests', 'pullRequest', 'description', 'isPrivate',
    'createdAt', 'updatedAt', 'url',
  ],
  Ref: ['name', 'prefix', 'target'],
  Commit: ['oid', 'message'],
  Issue: [
    'id', 'databaseId', 'number', 'title', 'state', 'body', 'author', 'labels', 'comments',
    'createdAt', 'updatedAt', 'url', 'closed',
  ],
  PullRequest: [
    'id', 'databaseId', 'number', 'title', 'state', 'body', 'merged', 'mergeable', 'headRefName',
    'baseRefName', 'headRef', 'baseRef', 'files', 'author', 'createdAt', 'updatedAt', 'mergedAt',
    'mergeCommit', 'url', 'closed',
  ],
  IssueConnection: ['nodes', 'edges', 'pageInfo', 'totalCount'],
  PullRequestConnection: ['nodes', 'edges', 'pageInfo', 'totalCount'],
  CommentConnection: ['nodes', 'edges', 'pageInfo', 'totalCount'],
  LabelConnection: ['nodes', 'edges', 'pageInfo', 'totalCount'],
  PullRequestFileConnection: ['nodes', 'edges', 'pageInfo', 'totalCount'],
  IssueEdge: ['node', 'cursor'],
  PullRequestEdge: ['node', 'cursor'],
  CommentEdge: ['node', 'cursor'],
  LabelEdge: ['node', 'cursor'],
  PageInfo: ['hasNextPage', 'hasPreviousPage', 'endCursor', 'startCursor'],
  PullRequestFile: ['path', 'additions', 'deletions', 'changeType'],
  Comment: ['id', 'body', 'author', 'createdAt'],
  Label: ['id', 'name', 'color'],
  CreateIssuePayload: ['issue', 'clientMutationId'],
  CloseIssuePayload: ['issue', 'clientMutationId'],
  CreatePullRequestPayload: ['pullRequest', 'clientMutationId'],
  MergePullRequestPayload: ['pullRequest', 'clientMutationId'],
  AddCommentPayload: ['commentEdge', 'clientMutationId'],
  __Type: ['name', 'kind', 'description', 'fields', 'enumValues', 'possibleTypes', 'inputFields', 'specifiedByURL'],
  __Field: ['name', 'description', 'args', 'type', 'isDeprecated', 'deprecationReason'],
  __EnumValue: ['name', 'description', 'isDeprecated', 'deprecationReason'],
  __InputValue: ['name', 'description', 'type', 'defaultValue'],
  __Schema: ['queryType', 'mutationType', 'subscriptionType', 'types', 'directives'],
  __Directive: ['name', 'description', 'locations', 'args'],
};

const ENUM_TYPES: Record<string, string[]> = {
  IssueState: ['OPEN', 'CLOSED'],
  PullRequestState: ['OPEN', 'CLOSED', 'MERGED'],
  MergeableState: ['MERGEABLE', 'CONFLICTING', 'UNKNOWN'],
  SearchType: ['ISSUE', 'REPOSITORY', 'USER'],
  IssueOrderField: ['CREATED_AT', 'UPDATED_AT', 'COMMENTS'],
  OrderDirection: ['ASC', 'DESC'],
  PullRequestMergeMethod: ['MERGE', 'SQUASH', 'REBASE'],
};

const SCALAR_TYPES = new Set(['String', 'Int', 'Float', 'Boolean', 'ID', 'DateTime', 'URI', 'GitObjectID', 'HTML', 'Base64String']);

type GqlObj = { $type: string } & Record<string, unknown>;

function wrap(type: string, props: Record<string, unknown>): GqlObj {
  return { $type: type, ...props };
}

function isGqlObj(value: unknown): value is GqlObj {
  return isRecord(value) && typeof value.$type === 'string';
}

function gid(type: string, ...parts: Array<string | number>): string {
  return Buffer.from(`${type}:${parts.join(':')}`, 'utf8').toString('base64');
}

function parseGid(id: unknown): { type: string; parts: string[] } | null {
  if (typeof id !== 'string') return null;
  try {
    const text = Buffer.from(id, 'base64').toString('utf8');
    const idx = text.indexOf(':');
    if (idx <= 0) return null;
    return { type: text.slice(0, idx), parts: text.slice(idx + 1).split(':') };
  } catch {
    return null;
  }
}

function repoByDbId(id: number): RepoRec | null {
  for (const repo of repos.values()) if (repo.id === id) return repo;
  return null;
}

function userWrap(): GqlObj {
  return wrap('User', {});
}

function repoWrap(repo: RepoRec): GqlObj {
  return wrap('Repository', { repo });
}

function issueWrap(repo: RepoRec, issue: IssueRec): GqlObj {
  return wrap('Issue', { repo, issue });
}

function pullWrap(repo: RepoRec, pull: PullRec): GqlObj {
  return wrap('PullRequest', { repo, pull });
}

function commentWrap(repo: RepoRec, issue: IssueRec, comment: CommentRec): GqlObj {
  return wrap('Comment', { repo, issue, comment });
}

function cursorFor(key: string | number): string {
  return Buffer.from(`cursor:${key}`, 'utf8').toString('base64');
}

function makeConnection(
  type: string,
  edgeType: string,
  nodes: GqlObj[],
  cursorOf: (node: GqlObj) => string,
  args: Record<string, unknown>,
): GqlObj {
  let start = 0;
  if (typeof args.after === 'string' && args.after !== '') {
    const idx = nodes.findIndex((n) => cursorOf(n) === args.after);
    if (idx >= 0) start = idx + 1;
  }
  const first = typeof args.first === 'number' && Number.isFinite(args.first) ? Math.max(0, Math.trunc(args.first)) : nodes.length;
  const slice = nodes.slice(start, start + first);
  const pageInfo = wrap('PageInfo', {
    hasNextPage: start + slice.length < nodes.length,
    hasPreviousPage: start > 0,
    endCursor: slice.length > 0 ? cursorOf(slice[slice.length - 1]!) : null,
    startCursor: slice.length > 0 ? cursorOf(slice[0]!) : null,
  });
  return wrap(type, {
    nodes: slice,
    edges: slice.map((node) => wrap(edgeType, { node, cursor: cursorOf(node) })),
    pageInfo,
    totalCount: nodes.length,
  });
}

function issueConnection(repo: RepoRec, args: Record<string, unknown>): GqlObj {
  let list = [...repo.issues.values()];
  if (Array.isArray(args.states)) {
    const states = args.states as unknown[];
    list = list.filter((i) => states.includes(i.state === 'open' ? 'OPEN' : 'CLOSED'));
  }
  const orderBy = isRecord(args.orderBy) ? args.orderBy : {};
  const direction = orderBy.direction === 'DESC' ? 'DESC' : 'ASC';
  list.sort((a, b) => (direction === 'DESC' ? b.number - a.number : a.number - b.number));
  return makeConnection('IssueConnection', 'IssueEdge', list.map((i) => issueWrap(repo, i)), (n) => cursorFor((n.issue as IssueRec).number), args);
}

function pullConnection(repo: RepoRec, args: Record<string, unknown>): GqlObj {
  let list = [...repo.pulls.values()];
  const stateOf = (p: PullRec): string => (p.merged ? 'MERGED' : p.state.toUpperCase());
  if (Array.isArray(args.states)) {
    const states = args.states as unknown[];
    list = list.filter((p) => states.includes(stateOf(p)));
  }
  const orderBy = isRecord(args.orderBy) ? args.orderBy : {};
  const direction = orderBy.direction === 'DESC' ? 'DESC' : 'ASC';
  list.sort((a, b) => (direction === 'DESC' ? b.number - a.number : a.number - b.number));
  return makeConnection('PullRequestConnection', 'PullRequestEdge', list.map((p) => pullWrap(repo, p)), (n) => cursorFor((n.pull as PullRec).number), args);
}

function pullFiles(repo: RepoRec, pull: PullRec): Array<{ path: string; additions: number; deletions: number; changeType: string }> {
  const baseTree = commitTree(pull.baseSha);
  const headTree = commitTree(branchTip(repo, pull.head) ?? pull.headSha);
  return diffTrees(baseTree, headTree).map((d) => {
    const beforeData = d.before === null ? null : (getObject(d.before)?.data ?? null);
    const afterData = d.after === null ? null : (getObject(d.after)?.data ?? null);
    return {
      path: d.path,
      additions: afterData === null ? 0 : lineCount(afterData),
      deletions: beforeData === null ? 0 : lineCount(beforeData),
      changeType: d.before === null ? 'ADDED' : d.after === null ? 'DELETED' : 'MODIFIED',
    };
  });
}

interface GqlCtx {
  vars: Record<string, unknown>;
  errors: Array<{ message: string }>;
  fragments: Map<string, { typeCondition: string; selection: GqlSelection[] }>;
}

function resolveNode(id: unknown): GqlObj | null {
  const parsed = parseGid(id);
  if (parsed === null) return null;
  if (parsed.type === 'Repository') {
    const repo = repoByDbId(Number(parsed.parts[0]));
    return repo === null ? null : repoWrap(repo);
  }
  if (parsed.type === 'Issue') {
    const repo = repoByDbId(Number(parsed.parts[0]));
    const issue = repo?.issues.get(Number(parsed.parts[1]));
    return repo !== null && repo !== undefined && issue !== undefined ? issueWrap(repo, issue) : null;
  }
  if (parsed.type === 'PullRequest') {
    const repo = repoByDbId(Number(parsed.parts[0]));
    const pull = repo?.pulls.get(Number(parsed.parts[1]));
    return repo !== null && repo !== undefined && pull !== undefined ? pullWrap(repo, pull) : null;
  }
  if (parsed.type === 'User') return userWrap();
  return null;
}

function typeKind(name: string): string | null {
  if (ENUM_TYPES[name] !== undefined) return 'ENUM';
  if (name === 'Node') return 'INTERFACE';
  if (TYPE_FIELDS[name] !== undefined) return 'OBJECT';
  if (SCALAR_TYPES.has(name)) return 'SCALAR';
  return null;
}

function resolveGqlField(typeName: string, source: GqlObj | null, field: string, args: Record<string, unknown>, ctx: GqlCtx): unknown {
  if (typeName === 'Query') {
    switch (field) {
      case 'viewer':
        return userWrap();
      case 'repository': {
        if (args.owner !== VIEWER_LOGIN || typeof args.name !== 'string') return null;
        const repo = repos.get(args.name);
        return repo === undefined ? null : repoWrap(repo);
      }
      case 'node':
        return resolveNode(args.id);
      case '__type':
        return typeof args.name === 'string' ? wrap('__Type', { name: args.name }) : null;
      case '__schema':
        return wrap('__Schema', {});
      default:
        return null;
    }
  }
  if (typeName === 'Mutation') {
    switch (field) {
      case 'createIssue': {
        const input = isRecord(args.input) ? args.input : {};
        const parsed = parseGid(input.repositoryId);
        const repo = parsed === null ? null : repoByDbId(Number(parsed.parts[0]));
        if (repo === null) {
          ctx.errors.push({ message: 'Repository not found' });
          return wrap('CreateIssuePayload', { issue: null, clientMutationId: input.clientMutationId ?? null });
        }
        const issue = createIssue(repo, str(input.title), str(input.body), []);
        return wrap('CreateIssuePayload', { issue: issueWrap(repo, issue), clientMutationId: input.clientMutationId ?? null });
      }
      case 'closeIssue': {
        const input = isRecord(args.input) ? args.input : {};
        const target = resolveNode(input.issueId);
        if (target === null || target.$type !== 'Issue') {
          ctx.errors.push({ message: 'Issue not found' });
          return wrap('CloseIssuePayload', { issue: null, clientMutationId: input.clientMutationId ?? null });
        }
        const issue = target.issue as IssueRec;
        issue.state = 'closed';
        return wrap('CloseIssuePayload', { issue: target, clientMutationId: input.clientMutationId ?? null });
      }
      case 'createPullRequest': {
        const input = isRecord(args.input) ? args.input : {};
        const parsed = parseGid(input.repositoryId);
        const repo = parsed === null ? null : repoByDbId(Number(parsed.parts[0]));
        if (repo === null) {
          ctx.errors.push({ message: 'Repository not found' });
          return wrap('CreatePullRequestPayload', { pullRequest: null, clientMutationId: input.clientMutationId ?? null });
        }
        const pull = createPull(repo, str(input.title), str(input.body), str(input.headRefName), str(input.baseRefName));
        if (pull === null) {
          ctx.errors.push({ message: 'Invalid head or base ref' });
          return wrap('CreatePullRequestPayload', { pullRequest: null, clientMutationId: input.clientMutationId ?? null });
        }
        return wrap('CreatePullRequestPayload', { pullRequest: pullWrap(repo, pull), clientMutationId: input.clientMutationId ?? null });
      }
      case 'mergePullRequest': {
        const input = isRecord(args.input) ? args.input : {};
        const target = resolveNode(input.pullRequestId);
        if (target === null || target.$type !== 'PullRequest') {
          ctx.errors.push({ message: 'Pull request not found' });
          return wrap('MergePullRequestPayload', { pullRequest: null, clientMutationId: input.clientMutationId ?? null });
        }
        const repo = target.repo as RepoRec;
        const pull = target.pull as PullRec;
        const result = mergePull(repo, pull);
        if (result === 'conflict') ctx.errors.push({ message: 'Pull request is not mergeable' });
        return wrap('MergePullRequestPayload', { pullRequest: target, clientMutationId: input.clientMutationId ?? null });
      }
      case 'addComment': {
        const input = isRecord(args.input) ? args.input : {};
        const target = resolveNode(input.subjectId);
        if (target === null || target.$type !== 'Issue') {
          ctx.errors.push({ message: 'Subject not found' });
          return wrap('AddCommentPayload', { commentEdge: null, clientMutationId: input.clientMutationId ?? null });
        }
        const repo = target.repo as RepoRec;
        const issue = target.issue as IssueRec;
        const comment: CommentRec = { id: issue.nextCommentId, body: str(input.body) };
        issue.nextCommentId += 1;
        issue.comments.push(comment);
        return wrap('AddCommentPayload', {
          commentEdge: wrap('CommentEdge', { node: commentWrap(repo, issue, comment), cursor: cursorFor(comment.id) }),
          clientMutationId: input.clientMutationId ?? null,
        });
      }
      default:
        return null;
    }
  }
  if (source === null) return null;
  switch (typeName) {
    case 'User':
      switch (field) {
        case 'login': return VIEWER_LOGIN;
        case 'id': return gid('User', VIEWER_ID);
        case 'databaseId': return VIEWER_ID;
        case 'name': return VIEWER_NAME;
        case 'email': return `${VIEWER_LOGIN}@example.invalid`;
        case 'url': return `https://forge.invalid/${VIEWER_LOGIN}`;
        default: return null;
      }
    case 'Repository': {
      const repo = source.repo as RepoRec;
      switch (field) {
        case 'id': return gid('Repository', repo.id);
        case 'databaseId': return repo.id;
        case 'name': return repo.name;
        case 'nameWithOwner': return `${VIEWER_LOGIN}/${repo.name}`;
        case 'owner': return userWrap();
        case 'description': return repo.description;
        case 'isPrivate': return repo.priv;
        case 'viewerPermission': return 'ADMIN';
        case 'hasIssuesEnabled': return true;
        case 'createdAt': return repo.createdAt;
        case 'updatedAt': return repo.createdAt;
        case 'url': return `https://forge.invalid/${VIEWER_LOGIN}/${repo.name}`;
        case 'defaultBranchRef': {
          const tip = branchTip(repo, DEFAULT_BRANCH);
          return tip === null ? null : wrap('Ref', { name: DEFAULT_BRANCH, oid: tip });
        }
        case 'issue': {
          const issue = typeof args.number === 'number' ? repo.issues.get(args.number) : undefined;
          return issue === undefined ? null : issueWrap(repo, issue);
        }
        case 'issues': return issueConnection(repo, args);
        case 'pullRequest': {
          const pull = typeof args.number === 'number' ? repo.pulls.get(args.number) : undefined;
          return pull === undefined ? null : pullWrap(repo, pull);
        }
        case 'pullRequests': return pullConnection(repo, args);
        default: return null;
      }
    }
    case 'Ref':
      switch (field) {
        case 'name': return source.name;
        case 'prefix': return 'refs/heads/';
        case 'target': return typeof source.oid === 'string' ? wrap('Commit', { oid: source.oid }) : null;
        default: return null;
      }
    case 'Commit': {
      const obj = getObject(source.oid as string);
      switch (field) {
        case 'oid': return source.oid;
        case 'message': return obj !== undefined && obj.type === 'commit' ? parseCommit(obj.data).message : '';
        default: return null;
      }
    }
    case 'Issue': {
      const repo = source.repo as RepoRec;
      const issue = source.issue as IssueRec;
      switch (field) {
        case 'id': return gid('Issue', repo.id, issue.number);
        case 'databaseId': return issue.id;
        case 'number': return issue.number;
        case 'title': return issue.title;
        case 'body': return issue.body;
        case 'state': return issue.state.toUpperCase();
        case 'closed': return issue.state === 'closed';
        case 'author': return userWrap();
        case 'createdAt': return repo.createdAt;
        case 'updatedAt': return repo.createdAt;
        case 'url': return `https://forge.invalid/${VIEWER_LOGIN}/${repo.name}/issues/${issue.number}`;
        case 'labels': {
          const nodes = issue.labels.map((name) => wrap('Label', { name, color: repo.labels.get(name)?.color ?? '000000', repo }));
          return makeConnection('LabelConnection', 'LabelEdge', nodes, (n) => cursorFor(n.name as string), args);
        }
        case 'comments': {
          const nodes = issue.comments.map((c) => commentWrap(repo, issue, c));
          return makeConnection('CommentConnection', 'CommentEdge', nodes, (n) => cursorFor((n.comment as CommentRec).id), args);
        }
        default: return null;
      }
    }
    case 'PullRequest': {
      const repo = source.repo as RepoRec;
      const pull = source.pull as PullRec;
      switch (field) {
        case 'id': return gid('PullRequest', repo.id, pull.number);
        case 'databaseId': return pull.id;
        case 'number': return pull.number;
        case 'title': return pull.title;
        case 'body': return pull.body;
        case 'state': return pull.merged ? 'MERGED' : pull.state.toUpperCase();
        case 'closed': return pull.state === 'closed';
        case 'merged': return pull.merged;
        case 'mergedAt': return pull.mergedAt;
        case 'mergeable':
          if (pull.state !== 'open') return 'UNKNOWN';
          return mergePullTree(repo, pull) !== null ? 'MERGEABLE' : 'CONFLICTING';
        case 'headRefName': return pull.head;
        case 'baseRefName': return pull.base;
        case 'headRef': return wrap('Ref', { name: pull.head, oid: branchTip(repo, pull.head) ?? pull.headSha });
        case 'baseRef': return wrap('Ref', { name: pull.base, oid: branchTip(repo, pull.base) ?? pull.baseSha });
        case 'mergeCommit': return pull.mergeSha === null ? null : wrap('Commit', { oid: pull.mergeSha });
        case 'author': return userWrap();
        case 'createdAt': return repo.createdAt;
        case 'updatedAt': return repo.createdAt;
        case 'url': return `https://forge.invalid/${VIEWER_LOGIN}/${repo.name}/pull/${pull.number}`;
        case 'files': {
          const nodes = pullFiles(repo, pull).map((f) => wrap('PullRequestFile', { ...f }));
          return makeConnection('PullRequestFileConnection', 'IssueEdge', nodes, (n) => cursorFor(n.path as string), args);
        }
        default: return null;
      }
    }
    case 'Comment': {
      const comment = source.comment as CommentRec;
      switch (field) {
        case 'id': return gid('Comment', (source.repo as RepoRec).id, (source.issue as IssueRec).number, comment.id);
        case 'body': return comment.body;
        case 'author': return userWrap();
        case 'createdAt': return (source.repo as RepoRec).createdAt;
        default: return null;
      }
    }
    case 'Label':
      switch (field) {
        case 'id': return gid('Label', (source.repo as RepoRec).id, source.name as string);
        case 'name': return source.name;
        case 'color': return source.color;
        default: return null;
      }
    case 'PullRequestFile':
      switch (field) {
        case 'path': return source.path;
        case 'additions': return source.additions;
        case 'deletions': return source.deletions;
        case 'changeType': return source.changeType;
        default: return null;
      }
    case 'PageInfo':
      return source[field] ?? null;
    case 'IssueConnection':
    case 'PullRequestConnection':
    case 'CommentConnection':
    case 'LabelConnection':
    case 'PullRequestFileConnection':
      return source[field] ?? null;
    case 'IssueEdge':
    case 'PullRequestEdge':
    case 'CommentEdge':
    case 'LabelEdge':
      return source[field] ?? null;
    case 'CreateIssuePayload':
    case 'CloseIssuePayload':
      return source[field] ?? null;
    case 'CreatePullRequestPayload':
    case 'MergePullRequestPayload':
      return source[field] ?? null;
    case 'AddCommentPayload':
      return source[field] ?? null;
    case '__Type': {
      const name = source.name as string;
      switch (field) {
        case 'name': return name;
        case 'kind': return typeKind(name);
        case 'description': return null;
        case 'fields': {
          const fields = TYPE_FIELDS[name];
          return fields === undefined ? null : fields.map((f) => wrap('__Field', { name: f }));
        }
        case 'enumValues': {
          const values = ENUM_TYPES[name];
          return values === undefined ? null : values.map((v) => wrap('__EnumValue', { name: v }));
        }
        case 'possibleTypes': return null;
        case 'inputFields': return null;
        case 'specifiedByURL': return null;
        default: return null;
      }
    }
    case '__Field':
      switch (field) {
        case 'name': return source.name;
        case 'description': return null;
        case 'args': return [];
        case 'type': return null;
        case 'isDeprecated': return false;
        case 'deprecationReason': return null;
        default: return null;
      }
    case '__EnumValue':
      switch (field) {
        case 'name': return source.name;
        case 'description': return null;
        case 'isDeprecated': return false;
        case 'deprecationReason': return null;
        default: return null;
      }
    case '__Schema':
      switch (field) {
        case 'queryType': return wrap('__Type', { name: 'Query' });
        case 'mutationType': return wrap('__Type', { name: 'Mutation' });
        case 'subscriptionType': return null;
        case 'types': return [...Object.keys(TYPE_FIELDS), ...Object.keys(ENUM_TYPES), ...SCALAR_TYPES].map((name) => wrap('__Type', { name }));
        case 'directives': return [];
        default: return null;
      }
    default:
      return null;
  }
}

function interfaceMatches(typeName: string, condition: string): boolean {
  if (condition === 'Node') return ['Repository', 'Issue', 'PullRequest', 'User', 'Comment', 'Label'].includes(typeName);
  return false;
}

function execSelectionSet(typeName: string, source: GqlObj | null, selections: readonly GqlSelection[], ctx: GqlCtx): Record<string, unknown> {
  const out: Record<string, unknown> = {};
  for (const sel of selections) {
    if (sel.kind === 'field') {
      const field = sel.field;
      const key = field.alias ?? field.name;
      if (field.name === '__typename') {
        out[key] = typeName;
        continue;
      }
      const fields = TYPE_FIELDS[typeName];
      if (fields === undefined || !fields.includes(field.name)) {
        ctx.errors.push({ message: `Field '${field.name}' doesn't exist on type '${typeName}'` });
        out[key] = null;
        continue;
      }
      const args: Record<string, unknown> = {};
      for (const [argName, argValue] of field.args) args[argName] = gqlValue(argValue, ctx.vars);
      const value = resolveGqlField(typeName, source, field.name, args, ctx);
      out[key] = completeGqlValue(value, field.selection, ctx);
    } else if (sel.kind === 'inline') {
      if (sel.typeCondition === undefined || sel.typeCondition === typeName || interfaceMatches(typeName, sel.typeCondition)) {
        Object.assign(out, execSelectionSet(typeName, source, sel.selection, ctx));
      }
    } else {
      const fragment = ctx.fragments.get(sel.name);
      if (fragment !== undefined && (fragment.typeCondition === typeName || interfaceMatches(typeName, fragment.typeCondition))) {
        Object.assign(out, execSelectionSet(typeName, source, fragment.selection, ctx));
      }
    }
  }
  return out;
}

function completeGqlValue(value: unknown, selection: readonly GqlSelection[] | undefined, ctx: GqlCtx): unknown {
  if (value === null || value === undefined) return null;
  if (Array.isArray(value)) return value.map((entry) => completeGqlValue(entry, selection, ctx));
  if (isGqlObj(value)) {
    if (selection === undefined) return {};
    return execSelectionSet(value.$type, value, selection, ctx);
  }
  return value;
}

function executeGraphQLOperation(op: Record<string, unknown>): Record<string, unknown> {
  const query = typeof op.query === 'string' ? op.query : '';
  const vars = isRecord(op.variables) ? op.variables : {};
  const operationName = typeof op.operationName === 'string' ? op.operationName : undefined;
  let doc: GqlDocument;
  try {
    doc = new GqlParser(query).parseDocument();
  } catch (err) {
    return { data: null, errors: [{ message: err instanceof Error ? err.message : String(err) }] };
  }
  const operation = doc.operations.find((o) => operationName === undefined || o.name === operationName) ?? doc.operations[0];
  if (operation === undefined) return { data: null, errors: [{ message: 'No operation found' }] };
  const ctx: GqlCtx = { vars, errors: [], fragments: doc.fragments };
  const data = execSelectionSet(operation.type === 'mutation' ? 'Mutation' : 'Query', null, operation.selection, ctx);
  const out: Record<string, unknown> = { data };
  if (ctx.errors.length > 0) out.errors = ctx.errors;
  return out;
}

async function handleGraphQL(req: IncomingMessage, res: ServerResponse): Promise<void> {
  if (!authorized(req)) {
    sendJson(res, 401, { message: 'Requires authentication' });
    return;
  }
  if ((req.method ?? 'GET') !== 'POST') {
    sendJson(res, 405, { message: 'Method Not Allowed' });
    return;
  }
  const raw = await readBody(req);
  const parsed = parseJsonBody(raw);
  if (!parsed.ok) {
    sendJson(res, 400, { errors: [{ message: 'Invalid JSON' }] });
    return;
  }
  if (Array.isArray(parsed.value)) {
    sendJson(res, 200, parsed.value.map((op) => executeGraphQLOperation(isRecord(op) ? op : {})));
    return;
  }
  if (isRecord(parsed.value)) {
    sendJson(res, 200, executeGraphQLOperation(parsed.value));
    return;
  }
  sendJson(res, 400, { errors: [{ message: 'Invalid request' }] });
}

export function createApp(): Server {
  return createServer((req: IncomingMessage, res: ServerResponse) => {
    void (async () => {
      try {
        const url = new URL(req.url ?? '/', 'http://entry');
        const path = url.pathname;
        const method = req.method ?? 'GET';

        if (method === 'GET' && path === '/healthz') {
          sendJson(res, 200, { ok: true });
          return;
        }
        if (path === '/api/v3' || path.startsWith('/api/v3/')) {
          await handleRest(req, res, url);
          return;
        }
        if (path === '/api/graphql') {
          await handleGraphQL(req, res);
          return;
        }
        if (path === '/mcp') {
          await handleMcp(req, res);
          return;
        }
        if (path.includes('.git/')) {
          await handleGitHttp(req, res, url);
          return;
        }
        sendJson(res, 404, { message: 'Not Found' });
      } catch {
        if (!res.headersSent) sendJson(res, 500, { message: 'Internal Server Error' });
        else res.end();
      }
    })();
  });
}
