// mend: one patch tool for every AI edit format.
//
// Reads a patch in one of four formats (unified diff, SEARCH/REPLACE blocks,
// V4A, JSON edits), finds the lines each edit names at the first of three
// matching tiers, and writes every change or none. SPEC.md is the contract.
// Node 22, standard library only; run as `node main.ts [options] [PATCH]`.
//
// In a trial the grader runs `node /bot/main.ts` with MAKEFUN_ENV_URL set,
// and this file hands over to runner.ts (the last lines below): keep them.

import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

/** A parse fault: the run answers `error: parse <line>` and exits 2. */
class ParseFault {
  readonly line: number;
  constructor(line: number) {
    this.line = line;
  }
}

/** One edit's failure: the run answers `error: <code> <path>` and exits 1. */
class EditFailure {
  readonly code: string;
  readonly path: string;
  constructor(code: string, path: string) {
    this.code = code;
    this.path = path;
  }
}

const isBlank = (s: string): boolean => s.trim() === '';

/** A patch's lines (SPEC.md section 3): split at `\n`, one trailing `\r` off each. */
function splitPatch(text: string): string[] {
  if (text === '') return [];
  const lines = text.split('\n');
  if (text.endsWith('\n')) lines.pop();
  return lines.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

/** A path is safe when it names a file under the tree (SPEC.md section 3). */
function isSafePath(p: string): boolean {
  return (
    p !== '' &&
    !p.startsWith('/') &&
    !p.includes('\\') &&
    p.split('/').every((s) => s !== '' && s !== '.' && s !== '..')
  );
}

function requireSafe(p: string): void {
  if (!isSafePath(p)) throw new EditFailure('unsafe', p);
}

/** A file's lines, its line break and whether it ends with one (section 3). */
interface TextFile {
  lines: string[];
  br: '\r\n' | '\n';
  finalBreak: boolean;
}

function readText(text: string): TextFile {
  if (text === '') return { lines: [], br: '\n', finalBreak: false };
  const nl = text.indexOf('\n');
  const br: '\r\n' | '\n' = nl > 0 && text[nl - 1] === '\r' ? '\r\n' : '\n';
  const parts = text.split(br);
  const finalBreak = text.endsWith(br);
  if (finalBreak) parts.pop();
  return { lines: parts, br, finalBreak };
}

function writeText(f: TextFile): string {
  if (f.lines.length === 0) return '';
  return f.lines.join(f.br) + (f.finalBreak ? f.br : '');
}

/** A file is CRLF when its first line feed follows a carriage return. */
function isCRLF(text: string): boolean {
  const nl = text.indexOf('\n');
  return nl > 0 && text[nl - 1] === '\r';
}

/**
 * The tree as the edits leave it. `now` holds the paths edits touched
 * (null: deleted); everything else is read from disk on first use.
 * `moves` records the move edits that succeeded, for the `R` output lines.
 */
class Tree {
  private readonly seen = new Map<string, string | null>();
  readonly now = new Map<string, string | null>();
  readonly moves: Array<[string, string]> = [];

  original(p: string): string | null {
    if (!this.seen.has(p)) {
      let v: string | null = null;
      try {
        if (statSync(p).isFile()) v = readFileSync(p, 'utf8');
      } catch {
        v = null;
      }
      this.seen.set(p, v);
    }
    return this.seen.get(p)!;
  }

  get(p: string): string | null {
    return this.now.has(p) ? this.now.get(p)! : this.original(p);
  }

  file(p: string): TextFile | null {
    const t = this.get(p);
    return t === null ? null : readText(t);
  }

  put(p: string, f: TextFile): void {
    this.now.set(p, writeText(f));
  }

  putText(p: string, text: string): void {
    this.now.set(p, text);
  }

  drop(p: string): void {
    this.now.set(p, null);
  }
}

/* ------------------------------------------------------------------ */
/* Matching lines (SPEC.md section 5)                                  */
/* ------------------------------------------------------------------ */

/** A line as a tier reads it: tier 1 drops trailing spaces/tabs, tier 2 both ends. */
function tierLine(s: string, tier: number): string {
  if (tier === 0) return s;
  const t = s.replace(/[ \t]+$/, '');
  return tier === 1 ? t : t.replace(/^[ \t]+/, '');
}

/** Every 0-based position where `pat` occurs in `lines` at `tier`, from `from` on. */
function occurrences(lines: string[], pat: string[], tier: number, from: number): number[] {
  const out: number[] = [];
  const n = pat.length;
  if (n === 0 || n > lines.length) return out;
  const want = pat.map((l) => tierLine(l, tier));
  for (let i = from; i + n <= lines.length; i++) {
    let ok = true;
    for (let j = 0; j < n; j++) {
      if (tierLine(lines[i + j]!, tier) !== want[j]) {
        ok = false;
        break;
      }
    }
    if (ok) out.push(i);
  }
  return out;
}

interface Found {
  tier: number;
  at: number[];
}

/** The first tier (0, 1, 2) at which `pat` occurs at or after `from`, if any. */
function findTier(lines: string[], pat: string[], from: number, strict: boolean): Found | null {
  const top = strict ? 0 : 2;
  for (let tier = 0; tier <= top; tier++) {
    const at = occurrences(lines, pat, tier, from);
    if (at.length > 0) return { tier, at };
  }
  return null;
}

const leadingWS = (s: string): string => {
  const m = /^[ \t]*/.exec(s);
  return m === null ? '' : m[0];
};

/**
 * One line of N: a context line, written as the file's own matched line
 * (the O index it stands for), or an added line, written as the patch has it.
 */
type NewLine = { ctx: number } | { add: string };

/**
 * The lines that replace a matched region. Context lines come from the file;
 * at tier 2 the added lines are re-indented: the leading spaces and tabs of
 * O's first line are replaced by those of the file's first matched line.
 */
function buildReplacement(file: TextFile, at: number, o: string[], n: NewLine[], tier: number): string[] {
  const out: string[] = [];
  const p = o.length > 0 ? leadingWS(o[0]!) : '';
  const f = leadingWS(file.lines[at] ?? '');
  for (const item of n) {
    if ('ctx' in item) {
      out.push(file.lines[at + item.ctx]!);
      continue;
    }
    const line = item.add;
    if (tier === 2 && line !== '' && !/^[ \t]+$/.test(line) && line.startsWith(p)) {
      out.push(f + line.slice(p.length));
    } else {
      out.push(line);
    }
  }
  return out;
}

/* ------------------------------------------------------------------ */
/* Unified diffs (SPEC.md section 6)                                   */
/* ------------------------------------------------------------------ */

interface Hunk {
  a: number;
  o: string[];
  n: NewLine[];
  /** a `\` line follows the hunk's last context or `+` line */
  noNL: boolean;
  /** a `\` line follows the hunk's last `+` line (for creations) */
  plusNoNL: boolean;
  hasPlus: boolean;
}

interface RawSection {
  gitOld: string | undefined;
  gitNew: string | undefined;
  pairOld: string | undefined;
  pairNew: string | undefined;
  renameFrom: string | undefined;
  renameTo: string | undefined;
  create: boolean;
  remove: boolean;
  hunks: Hunk[];
}

const HUNK_RE = /^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@/;
const GIT_RE = /^diff --git a\/(\S+) b\/(\S+)$/;

/** The path a `--- ` / `+++ ` line names: after the four characters, to the first tab, trimmed. */
function headerPath(line: string): string {
  let p = line.slice(4);
  const tab = p.indexOf('\t');
  if (tab >= 0) p = p.slice(0, tab);
  return p.trim();
}

/** A leading `a/` or `b/` is removed; `/dev/null` means no file. */
function sectionPath(p: string): string | null {
  if (p === '/dev/null') return null;
  if (p.startsWith('a/') || p.startsWith('b/')) return p.slice(2);
  return p;
}

/** A hunk from its header match and its body lines. */
function buildHunk(m: RegExpExecArray, body: string[]): Hunk {
  const o: string[] = [];
  const n: NewLine[] = [];
  let lastContent = -1;
  let lastPlus = -1;
  for (let k = 0; k < body.length; k++) {
    const l = body[k]!;
    if (l.startsWith(' ') || l === '') {
      o.push(l === '' ? '' : l.slice(1));
      n.push({ ctx: o.length - 1 });
      lastContent = k;
    } else if (l.startsWith('-')) {
      o.push(l.slice(1));
    } else if (l.startsWith('+')) {
      n.push({ add: l.slice(1) });
      lastContent = k;
      lastPlus = k;
    }
    // `\` lines only mark the line before them; they add nothing.
  }
  const after = (idx: number): boolean =>
    idx >= 0 && idx + 1 < body.length && body[idx + 1]!.startsWith('\\');
  return {
    a: parseInt(m[1]!, 10),
    o,
    n,
    noNL: after(lastContent),
    plusNoNL: after(lastPlus),
    hasPlus: lastPlus >= 0,
  };
}

/** Apply a section's hunks in order to a file's lines (section 6). */
function applyHunks(file: TextFile, hunks: Hunk[], strict: boolean, failPath: string): void {
  let d = 0;
  for (const h of hunks) {
    if (h.o.length === 0) {
      const oldLen = file.lines.length;
      const at = Math.min(Math.max(h.a + d, 0), oldLen);
      const ins = buildReplacement(file, at, h.o, h.n, 0);
      file.lines.splice(at, 0, ...ins);
      if (at === oldLen) file.finalBreak = !h.noNL;
      d += ins.length;
      continue;
    }
    const found = findTier(file.lines, h.o, 0, strict);
    if (found === null) throw new EditFailure('no-match', failPath);
    const target = h.a - 1 + d;
    let best = found.at[0]!;
    let bestDist = Math.abs(best - target);
    for (const pos of found.at) {
      const dist = Math.abs(pos - target);
      if (dist < bestDist) {
        best = pos;
        bestDist = dist;
      }
    }
    const at = best;
    const oldLen = file.lines.length;
    const repl = buildReplacement(file, at, h.o, h.n, found.tier);
    file.lines.splice(at, h.o.length, ...repl);
    if (at + h.o.length === oldLen) file.finalBreak = !h.noNL;
    d += repl.length - h.o.length;
  }
}

/** One unified section as one edit. */
function unifiedEdit(s: RawSection, strict: boolean): (tree: Tree) => void {
  const oldP = s.pairOld !== undefined ? sectionPath(s.pairOld) : s.renameFrom !== undefined ? s.renameFrom : s.gitOld !== undefined ? s.gitOld : null;
  const newP = s.pairNew !== undefined ? sectionPath(s.pairNew) : s.renameTo !== undefined ? s.renameTo : s.gitNew !== undefined ? s.gitNew : null;
  const create = s.create || oldP === null;
  const remove = !create && (s.remove || newP === null);
  const move = !create && !remove && oldP !== newP;
  if (create) {
    return (tree) => {
      const target = newP ?? '/dev/null';
      requireSafe(target);
      if (tree.get(target) !== null) throw new EditFailure('exists', target);
      const plus: string[] = [];
      let noNL = false;
      for (const h of s.hunks) {
        for (const item of h.n) if ('add' in item) plus.push(item.add);
        if (h.hasPlus) noNL = h.plusNoNL;
      }
      tree.put(target, { lines: plus, br: '\n', finalBreak: plus.length > 0 && !noNL });
    };
  }
  if (remove) {
    const target = oldP as string;
    return (tree) => {
      requireSafe(target);
      if (tree.get(target) === null) throw new EditFailure('missing', target);
      tree.drop(target);
    };
  }
  if (move) {
    const src = oldP as string;
    const dst = newP as string;
    return (tree) => {
      requireSafe(src);
      requireSafe(dst);
      const before = tree.get(src);
      if (before === null) throw new EditFailure('missing', src);
      if (tree.get(dst) !== null) throw new EditFailure('exists', dst);
      const file = readText(before);
      applyHunks(file, s.hunks, strict, src);
      tree.put(dst, file);
      tree.drop(src);
      tree.moves.push([src, dst]);
    };
  }
  const target = oldP as string;
  return (tree) => {
    requireSafe(target);
    const before = tree.get(target);
    if (before === null) throw new EditFailure('missing', target);
    const file = readText(before);
    applyHunks(file, s.hunks, strict, target);
    tree.put(target, file);
  };
}

/** Read a patch as a unified diff; throws ParseFault on a bad patch. */
function parseUnified(lines: string[], strict: boolean): Array<(tree: Tree) => void> {
  const n = lines.length;
  const sections: RawSection[] = [];
  let cur: RawSection | null = null;
  let state: 'out' | 'head' | 'post' = 'out';
  let i = 0;

  const finishSection = (): void => {
    if (cur !== null) {
      sections.push(cur);
      cur = null;
    }
  };
  const gitPaths = (line: string, idx: number): { old: string; new: string } => {
    const m = GIT_RE.exec(line);
    if (m === null) throw new ParseFault(idx + 1);
    return { old: m[1]!, new: m[2]! };
  };
  const startGitSection = (line: string, idx: number): void => {
    const g = gitPaths(line, idx);
    finishSection();
    cur = { gitOld: g.old, gitNew: g.new, pairOld: undefined, pairNew: undefined, renameFrom: undefined, renameTo: undefined, create: false, remove: false, hunks: [] };
    state = 'head';
  };
  const collectBody = (): string[] => {
    const body: string[] = [];
    while (i < n) {
      const l = lines[i]!;
      if (l.startsWith('diff --git ')) break;
      if (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) break;
      if (l === '' || l.startsWith(' ') || l.startsWith('-') || l.startsWith('+') || l.startsWith('\\')) {
        body.push(l);
        i++;
      } else break;
    }
    while (body.length > 0 && body[body.length - 1] === '') body.pop();
    return body;
  };
  const takeHunk = (): void => {
    const m = HUNK_RE.exec(lines[i]!);
    if (m === null) throw new ParseFault(i + 1);
    i++;
    const body = collectBody();
    cur!.hunks.push(buildHunk(m, body));
    state = 'post';
  };

  while (i < n) {
    const line = lines[i]!;
    if (state === 'out') {
      if (line.startsWith('diff --git ')) {
        startGitSection(line, i);
        i++;
      } else if (line.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) {
        finishSection();
        cur = { gitOld: undefined, gitNew: undefined, pairOld: headerPath(line), pairNew: headerPath(lines[i + 1]!), renameFrom: undefined, renameTo: undefined, create: false, remove: false, hunks: [] };
        state = 'head';
        i += 2;
      } else if (line.startsWith('@@')) {
        throw new ParseFault(i + 1);
      } else {
        i++;
      }
    } else if (state === 'head') {
      if (line.startsWith('diff --git ')) {
        startGitSection(line, i);
        i++;
      } else if (line.startsWith('--- ')) {
        if ((lines[i + 1] ?? '').startsWith('+++ ')) {
          if (cur!.pairOld !== undefined) {
            finishSection();
            cur = { gitOld: undefined, gitNew: undefined, pairOld: headerPath(line), pairNew: headerPath(lines[i + 1]!), renameFrom: undefined, renameTo: undefined, create: false, remove: false, hunks: [] };
            state = 'head';
          } else {
            cur!.pairOld = headerPath(line);
            cur!.pairNew = headerPath(lines[i + 1]!);
          }
          i += 2;
        } else {
          throw new ParseFault(i + 2);
        }
      } else if (line.startsWith('@@')) {
        takeHunk();
      } else if (line.startsWith('rename from ')) {
        cur!.renameFrom = line.slice('rename from '.length).trim();
        i++;
      } else if (line.startsWith('rename to ')) {
        cur!.renameTo = line.slice('rename to '.length).trim();
        i++;
      } else if (line.startsWith('new file mode')) {
        cur!.create = true;
        i++;
      } else if (line.startsWith('deleted file mode')) {
        cur!.remove = true;
        i++;
      } else {
        i++;
      }
    } else {
      if (line.startsWith('diff --git ')) {
        startGitSection(line, i);
        i++;
      } else if (line.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) {
        finishSection();
        cur = { gitOld: undefined, gitNew: undefined, pairOld: headerPath(line), pairNew: headerPath(lines[i + 1]!), renameFrom: undefined, renameTo: undefined, create: false, remove: false, hunks: [] };
        state = 'head';
        i += 2;
      } else if (line.startsWith('@@')) {
        takeHunk();
      } else {
        i++;
      }
    }
  }
  finishSection();
  return sections.map((s) => unifiedEdit(s, strict));
}

/* ------------------------------------------------------------------ */
/* SEARCH/REPLACE blocks (SPEC.md section 7)                           */
/* ------------------------------------------------------------------ */

function srEdit(path: string, oldLines: string[], newLines: string[], strict: boolean): (tree: Tree) => void {
  return (tree) => {
    requireSafe(path);
    if (oldLines.length === 0) {
      if (tree.get(path) !== null) throw new EditFailure('exists', path);
      tree.put(path, { lines: [...newLines], br: '\n', finalBreak: newLines.length > 0 });
      return;
    }
    const before = tree.get(path);
    if (before === null) throw new EditFailure('missing', path);
    const file = readText(before);
    const found = findTier(file.lines, oldLines, 0, strict);
    if (found === null) throw new EditFailure('no-match', path);
    if (found.at.length > 1) throw new EditFailure('ambiguous', path);
    const repl = buildReplacement(file, found.at[0]!, oldLines, newLines.map((l) => ({ add: l })), found.tier);
    file.lines.splice(found.at[0]!, oldLines.length, ...repl);
    tree.put(path, file);
  };
}

/** Read a patch as SEARCH/REPLACE blocks; throws ParseFault on a bad patch. */
function parseSearchReplace(lines: string[], strict: boolean): Array<(tree: Tree) => void> {
  const edits: Array<(tree: Tree) => void> = [];
  const n = lines.length;
  let prevEnd = -1;
  let prevPath: string | null = null;
  let i = 0;
  while (i < n) {
    let s = -1;
    for (let j = i; j < n; j++) {
      if (lines[j]!.trimEnd() === '<<<<<<< SEARCH') {
        s = j;
        break;
      }
    }
    if (s < 0) break;
    let eq = -1;
    for (let j = s + 1; j < n; j++) {
      if (lines[j]!.trimEnd() === '=======') {
        eq = j;
        break;
      }
    }
    if (eq < 0) throw new ParseFault(s + 1);
    let rep = -1;
    for (let j = eq + 1; j < n; j++) {
      if (lines[j]!.trimEnd() === '>>>>>>> REPLACE') {
        rep = j;
        break;
      }
    }
    if (rep < 0) throw new ParseFault(s + 1);
    let path: string | null = null;
    for (let j = s - 1; j > prevEnd; j--) {
      const l = lines[j]!;
      if (isBlank(l)) continue;
      const t = l.trim();
      if (t.startsWith('```')) continue;
      path = t;
      break;
    }
    if (path === null) {
      if (prevPath === null) throw new ParseFault(s + 1);
      path = prevPath;
    }
    edits.push(srEdit(path, lines.slice(s + 1, eq), lines.slice(eq + 1, rep), strict));
    prevPath = path;
    prevEnd = rep;
    i = rep + 1;
  }
  return edits;
}

/* ------------------------------------------------------------------ */
/* V4A patches (SPEC.md section 8)                                     */
/* ------------------------------------------------------------------ */

interface VChunk {
  anchor: string | null;
  endFile: boolean;
  o: string[];
  n: NewLine[];
}

interface VSection {
  kind: 'add' | 'delete' | 'update';
  path: string;
  headerIdx: number;
  content: Array<{ text: string; idx: number }>;
}

/** The first line at or after `from` equal to a one-line anchor, at the first tier with one. */
function findAnchor(lines: string[], anchor: string, from: number, strict: boolean): number | null {
  const top = strict ? 0 : 2;
  for (let tier = 0; tier <= top; tier++) {
    for (let i = from; i < lines.length; i++) {
      if (tierLine(lines[i]!, tier) === tierLine(anchor, tier)) return i;
    }
  }
  return null;
}

/** The first occurrence of O at or after `from`, at the first tier with one (end-of-file chunks only take one ending at the last line). */
function findChunk(lines: string[], o: string[], from: number, strict: boolean, endFile: boolean): { tier: number; at: number } | null {
  const top = strict ? 0 : 2;
  for (let tier = 0; tier <= top; tier++) {
    for (const at of occurrences(lines, o, tier, from)) {
      if (!endFile || at + o.length === lines.length) return { tier, at };
    }
  }
  return null;
}

function v4aEdit(s: VSection, strict: boolean): (tree: Tree) => void {
  if (s.kind === 'add') {
    const fileLines: string[] = [];
    for (const { text, idx } of s.content) {
      if (text === '') fileLines.push('');
      else if (text.startsWith('+')) fileLines.push(text.slice(1));
      else throw new ParseFault(idx + 1);
    }
    return (tree) => {
      requireSafe(s.path);
      if (tree.get(s.path) !== null) throw new EditFailure('exists', s.path);
      tree.put(s.path, { lines: fileLines, br: '\n', finalBreak: fileLines.length > 0 });
    };
  }
  if (s.kind === 'delete') {
    if (s.content.length > 0) throw new ParseFault(s.content[0]!.idx + 1);
    return (tree) => {
      requireSafe(s.path);
      if (tree.get(s.path) === null) throw new EditFailure('missing', s.path);
      tree.drop(s.path);
    };
  }
  let moveTo: string | null = null;
  let k = 0;
  if (s.content.length > 0 && s.content[0]!.text.startsWith('*** Move to: ')) {
    moveTo = s.content[0]!.text.slice('*** Move to: '.length).trim();
    k = 1;
  }
  const chunks: VChunk[] = [];
  let chunk: VChunk | null = null;
  const closeChunk = (): void => {
    if (chunk !== null) {
      chunks.push(chunk);
      chunk = null;
    }
  };
  for (; k < s.content.length; k++) {
    const { text, idx } = s.content[k]!;
    if (text.startsWith('@@')) {
      closeChunk();
      const anchor = text.slice(2).trim();
      chunk = { anchor: anchor === '' ? null : anchor, endFile: false, o: [], n: [] };
    } else if (text === '*** End of File') {
      if (chunk === null) throw new ParseFault(idx + 1);
      chunk.endFile = true;
      closeChunk();
    } else if (text.startsWith(' ') || text.startsWith('-') || text.startsWith('+') || text === '') {
      if (chunk === null) {
        if (chunks.length > 0) throw new ParseFault(idx + 1);
        chunk = { anchor: null, endFile: false, o: [], n: [] };
      }
      if (text.startsWith(' ') || text === '') {
        chunk.o.push(text === '' ? '' : text.slice(1));
        chunk.n.push({ ctx: chunk.o.length - 1 });
      } else if (text.startsWith('-')) {
        chunk.o.push(text.slice(1));
      } else {
        chunk.n.push({ add: text.slice(1) });
      }
    } else {
      throw new ParseFault(idx + 1);
    }
  }
  closeChunk();
  if (chunks.length === 0 && moveTo === null) throw new ParseFault(s.headerIdx + 1);
  const path = s.path;
  return (tree) => {
    requireSafe(path);
    if (moveTo !== null) requireSafe(moveTo);
    const before = tree.get(path);
    if (before === null) throw new EditFailure('missing', path);
    if (moveTo !== null && tree.get(moveTo) !== null) throw new EditFailure('exists', moveTo);
    const file = readText(before);
    let cursor = 0;
    for (const ch of chunks) {
      if (ch.anchor !== null) {
        const at = findAnchor(file.lines, ch.anchor, cursor, strict);
        if (at === null) throw new EditFailure('no-match', path);
        cursor = at + 1;
      }
      if (ch.o.length === 0) {
        const at = ch.endFile ? file.lines.length : cursor;
        const ins = ch.n.map((item) => ('add' in item ? item.add : ''));
        file.lines.splice(at, 0, ...ins);
        cursor = at + ins.length;
      } else {
        const found = findChunk(file.lines, ch.o, cursor, strict, ch.endFile);
        if (found === null) throw new EditFailure('no-match', path);
        const repl = buildReplacement(file, found.at, ch.o, ch.n, found.tier);
        file.lines.splice(found.at, ch.o.length, ...repl);
        cursor = found.at + repl.length;
      }
    }
    if (moveTo !== null) {
      tree.put(moveTo, file);
      tree.drop(path);
      tree.moves.push([path, moveTo]);
    } else {
      tree.put(path, file);
    }
  };
}

/** Read a patch as V4A; throws ParseFault on a bad patch. */
function parseV4a(lines: string[], strict: boolean): Array<(tree: Tree) => void> {
  const n = lines.length;
  let first = -1;
  for (let j = 0; j < n; j++) {
    if (!isBlank(lines[j]!)) {
      first = j;
      break;
    }
  }
  if (first < 0) throw new ParseFault(1);
  if (lines[first]!.trim() !== '*** Begin Patch') throw new ParseFault(first + 1);
  let last = -1;
  for (let j = n - 1; j >= 0; j--) {
    if (!isBlank(lines[j]!)) {
      last = j;
      break;
    }
  }
  if (lines[last]!.trim() !== '*** End Patch') throw new ParseFault(n + 1);
  const sections: VSection[] = [];
  let cur: VSection | null = null;
  const closeSection = (): void => {
    if (cur !== null) {
      while (cur.content.length > 0 && isBlank(cur.content[cur.content.length - 1]!.text)) cur.content.pop();
      sections.push(cur);
      cur = null;
    }
  };
  for (let j = first + 1; j < last; j++) {
    const l = lines[j]!;
    if (l.startsWith('*** Add File: ') || l.startsWith('*** Delete File: ') || l.startsWith('*** Update File: ')) {
      closeSection();
      const kind = l.startsWith('*** Add') ? 'add' : l.startsWith('*** Delete') ? 'delete' : 'update';
      cur = { kind, path: l.slice(l.indexOf(': ') + 2).trim(), headerIdx: j, content: [] };
    } else if (cur === null) {
      if (isBlank(l)) continue;
      throw new ParseFault(j + 1);
    } else {
      cur.content.push({ text: l, idx: j });
    }
  }
  closeSection();
  return sections.map((s) => v4aEdit(s, strict));
}

/* ------------------------------------------------------------------ */
/* JSON edits (SPEC.md section 9)                                      */
/* ------------------------------------------------------------------ */

/** One JSON edit object, or null when it is not one. */
function jsonEdit(v: unknown): ((tree: Tree) => void) | null {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) return null;
  const o = v as Record<string, unknown>;
  const p = o.path;
  if (typeof p !== 'string') return null;
  if (o.command === 'create') {
    if (typeof o.file_text !== 'string') return null;
    const text = o.file_text;
    return (tree) => {
      requireSafe(p);
      if (tree.get(p) !== null) throw new EditFailure('exists', p);
      tree.putText(p, text);
    };
  }
  if (o.command === 'str_replace') {
    if (typeof o.old_str !== 'string' || o.old_str === '') return null;
    if (o.new_str !== undefined && typeof o.new_str !== 'string') return null;
    const oldStr = o.old_str;
    const newStr = (o.new_str as string | undefined) ?? '';
    return (tree) => {
      requireSafe(p);
      const before = tree.get(p);
      if (before === null) throw new EditFailure('missing', p);
      const crlf = isCRLF(before);
      const toLF = (s: string): string => (crlf ? s.replaceAll('\r\n', '\n') : s);
      const t = toLF(before);
      const old = toLF(oldStr);
      let count = 0;
      let at = -1;
      for (let k = t.indexOf(old); k >= 0; k = t.indexOf(old, k + 1)) {
        count++;
        if (at < 0) at = k;
      }
      if (count === 0) throw new EditFailure('no-match', p);
      if (count > 1) throw new EditFailure('ambiguous', p);
      const out = t.slice(0, at) + toLF(newStr) + t.slice(at + old.length);
      tree.putText(p, crlf ? out.replaceAll('\n', '\r\n') : out);
    };
  }
  if (o.command === 'insert') {
    if (typeof o.insert_line !== 'number' || !Number.isInteger(o.insert_line)) return null;
    if (typeof o.new_str !== 'string') return null;
    const line = o.insert_line;
    const add = splitPatch(o.new_str);
    return (tree) => {
      requireSafe(p);
      const before = tree.get(p);
      if (before === null) throw new EditFailure('missing', p);
      const file = readText(before);
      if (line < 0 || line > file.lines.length) throw new EditFailure('no-match', p);
      file.lines.splice(line, 0, ...add);
      tree.put(p, file);
    };
  }
  return null;
}

/** Read a patch as JSON (array form or JSON Lines); throws ParseFault on a bad patch. */
function readJson(text: string, lines: string[]): Array<(tree: Tree) => void> {
  const first = lines.findIndex((l) => !isBlank(l));
  if (first < 0) throw new ParseFault(1);
  const edits: Array<(tree: Tree) => void> = [];
  if (lines[first]!.trimStart().startsWith('[')) {
    let v: unknown;
    try {
      v = JSON.parse(text);
    } catch {
      throw new ParseFault(first + 1);
    }
    if (!Array.isArray(v)) throw new ParseFault(first + 1);
    for (const x of v) {
      const e = jsonEdit(x);
      if (e === null) throw new ParseFault(first + 1);
      edits.push(e);
    }
    return edits;
  }
  lines.forEach((l, i) => {
    if (isBlank(l)) return;
    let e: ((tree: Tree) => void) | null = null;
    try {
      e = jsonEdit(JSON.parse(l));
    } catch {
      e = null;
    }
    if (e === null) throw new ParseFault(i + 1);
    edits.push(e);
  });
  return edits;
}

/* ------------------------------------------------------------------ */
/* Detecting the format (SPEC.md section 4)                           */
/* ------------------------------------------------------------------ */

function detectFormat(lines: string[]): string | null {
  const first = lines.findIndex((l) => !isBlank(l));
  if (first < 0) return null;
  if (lines[first]!.trim() === '*** Begin Patch') return 'v4a';
  const c = lines[first]!.trimStart()[0];
  if (c === '[' || c === '{') return 'json';
  if (lines.some((l) => l.trimEnd() === '<<<<<<< SEARCH')) return 'search-replace';
  if (
    lines.some(
      (l, i) =>
        l.startsWith('diff --git ') ||
        (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')),
    )
  ) {
    return 'unified';
  }
  return null;
}

function readPatch(kind: string, text: string, lines: string[], strict: boolean): Array<(tree: Tree) => void> {
  if (kind === 'json') return readJson(text, lines);
  if (kind === 'unified') return parseUnified(lines, strict);
  if (kind === 'search-replace') return parseSearchReplace(lines, strict);
  return parseV4a(lines, strict);
}

/* ------------------------------------------------------------------ */
/* Invocation, output and exit codes (SPEC.md sections 1, 2 and 10)    */
/* ------------------------------------------------------------------ */

type Edit = (tree: Tree) => void;

function run(args: string[]): { code: number; out: string[] } {
  let format: string | null = null;
  let check = false;
  let strict = false;
  const pos: string[] = [];
  let ended = false;
  for (const a of args) {
    if (!ended && a === '--') {
      ended = true;
    } else if (!ended && a.startsWith('-') && a !== '-') {
      if (a.startsWith('--format=') && format === null && FORMATS.includes(a.slice(9))) {
        format = a.slice(9);
      } else if (a === '--check' && !check) {
        check = true;
      } else if (a === '--strict' && !strict) {
        strict = true;
      } else {
        return { code: 2, out: ['error: usage'] };
      }
    } else {
      pos.push(a);
    }
  }
  if (pos.length > 1) return { code: 2, out: ['error: usage'] };
  const patchArg = pos.length === 0 || pos[0] === '-' ? null : pos[0]!;
  let text = '';
  try {
    text = readFileSync(patchArg ?? 0, 'utf8');
  } catch {
    if (patchArg !== null) return { code: 2, out: ['error: no-patch'] };
  }
  const lines = splitPatch(text);
  const kind = format === null || format === 'auto' ? detectFormat(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };
  let edits: Edit[];
  try {
    edits = readPatch(kind, text, lines, strict);
  } catch (e) {
    if (e instanceof ParseFault) return { code: 2, out: [`error: parse ${e.line}`] };
    throw e;
  }
  if (edits.length === 0) return { code: 2, out: ['error: parse 1'] };
  const tree = new Tree();
  const fails: EditFailure[] = [];
  for (const edit of edits) {
    const snapNow = new Map(tree.now);
    const snapMoves = tree.moves.length;
    try {
      edit(tree);
    } catch (e) {
      if (!(e instanceof EditFailure)) throw e;
      tree.now.clear();
      for (const [k, v] of snapNow) tree.now.set(k, v);
      tree.moves.length = snapMoves;
      fails.push(e);
    }
  }
  if (fails.length > 0) {
    return {
      code: 1,
      out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`],
    };
  }
  interface Row {
    key: string;
    text: string;
  }
  const rows: Row[] = [];
  const covered = new Set<string>();
  for (const [oldP, newP] of tree.moves) {
    if (tree.original(oldP) !== null && tree.get(oldP) === null && tree.original(newP) === null && tree.get(newP) !== null) {
      rows.push({ key: newP, text: `R ${oldP} -> ${newP}` });
      covered.add(oldP);
      covered.add(newP);
    }
  }
  for (const p of tree.now.keys()) {
    if (covered.has(p)) continue;
    const was = tree.original(p);
    const now = tree.now.get(p)!;
    if (was === now) continue;
    rows.push({ key: p, text: `${was === null ? 'A' : now === null ? 'D' : 'M'} ${p}` });
  }
  rows.sort((a, b) => Buffer.compare(Buffer.from(a.key, 'utf8'), Buffer.from(b.key, 'utf8')));
  const outLines = rows.map((r) => r.text);
  if (!check) {
    const keys = [...tree.now.keys()].sort((a, b) => Buffer.compare(Buffer.from(a, 'utf8'), Buffer.from(b, 'utf8')));
    for (const p of keys) {
      const was = tree.original(p);
      const now = tree.now.get(p)!;
      if (was === now) continue;
      if (now === null) {
        rmSync(p, { force: true });
      } else {
        mkdirSync(dirname(p), { recursive: true });
        writeFileSync(p, now);
      }
    }
  }
  return { code: 0, out: [...outLines, `ok: ${outLines.length} ${outLines.length === 1 ? 'file' : 'files'}`] };
}

const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  // A trial: the kit's runner reads the checks from the env and runs this file on each one, without this variable.
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const r = run(process.argv.slice(2));
  writeSync(1, r.out.map((l) => `${l}\n`).join(''));
  process.exitCode = r.code;
}
