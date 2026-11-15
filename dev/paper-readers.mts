// The paper-reader test (the parity skill, .claude/skills/parity/, whose
// section of that name states the procedure): readers that have only the note "Tolerant frames" say whether each
// example verifies, and their verdicts are compared with each case's declared
// outcome. This tool prepares the readers' directory and compares their
// answers; the readers themselves are run by whoever orchestrates.
//
//   node dev/paper-readers.mts prepare --out <dir> [--cases <file> | --pattern <s> …]
//                                      [--sample <n>] [--seed <k>] [--batch <size>] [--note <file>]
//   node dev/paper-readers.mts compare --dir <dir> [--json]
//
// `prepare` selects cases of `pipeline/cases.mts` (by the names listed one
// per line in `--cases`, by substrings of their names given with `--pattern`,
// or all), shuffles them by the seed, keeps the first `--sample` and writes
// into <dir>, which must lie outside the repository and be empty or absent:
// `paper.tex` (the note, or `--note`), `TASK.md`, `examples/<id>.ts` (each
// case's source with its comments removed, but for a JSDoc comment carrying
// an annotation tag) and `batch-<n>.txt` (the ids of each reader's batch).
// The key, id → case, declared outcome and area text, goes to `<dir>.key.json`
// beside the directory, where a reader working inside it does not look.
//
// `compare` reads the key and every `answers-*.json` of the directory and
// prints, per example, the case, the declared outcome, the reader's verdict
// and whether they agree: a positive case is expected to verify, a negative
// case or a gap to be refused, and a reader's "not covered" is counted
// apart. It prints the functions of every example that does not agree, the
// totals, and the totals per pattern P1, P2, … that an area text names.
// A disagreement leaves the exit status 0; a malformed answer or key is an
// error naming its file and id.
import { existsSync, mkdirSync, readdirSync, readFileSync, realpathSync, writeFileSync } from "node:fs";
import { basename, dirname, join, relative, resolve, isAbsolute } from "node:path";
import { cases, type Case } from "../pipeline/cases.mts";

const repository = resolve(dirname(import.meta.filename), "..");
const defaultNote = join(repository, "docs/drafts/tolerant-frames-note/note.tex");

type Verdict = "verifies" | "refused" | "not covered";
type Kind = Case["kind"];
type Confidence = "high" | "medium" | "low";
type Result = "agree" | "differ" | "not covered" | "unanswered";

interface KeyEntry {
  case: string;
  kind: Kind;
  area: string;
}

interface FunctionAnswer {
  name: string;
  verdict: Verdict;
  first_failing: string | null;
}

interface Answer {
  id: string;
  verdict: Verdict;
  functions: FunctionAnswer[];
  rules: string[];
  assumed: string[];
  why: string;
  confidence: Confidence;
}

const TASK = `# Task: judge examples from the paper alone

You have one paper, \`paper.tex\` in this directory (LaTeX source of "Tolerant frames"), and TypeScript examples under \`examples/\`. For each example assigned to you, answer the question a reader of the paper would answer: **does this example verify?**

Rules of the exercise:
- Read \`paper.tex\` in full first. Use ONLY the paper and the example files assigned to you. Do not read any other file on this machine (in particular no \`answers-*.json\`), do not search the web, do not run any tool on the examples. You have no access to the verifier and must not look for it.
- Judge by what the paper states. Its section "What verifies" defines the verdict, the surface syntax, the obligations and what the verifier knows at each point; use it as the procedure, and the rest of the paper as it directs. Where the paper says a rule is stated but not applied by the verifier, do not apply it.
- If answering needs a rule or notion the paper does not give (for example promises, classes, a library function it does not specify), answer "not covered" and name what is missing. Do not guess the verifier's behaviour.
- Whenever you had to choose between two readings of the paper, or assume something it does not state, say so in the \`assumed\` field: this is as important as the verdict.

Output: write ONE file \`answers-<your batch name>.json\` in this directory, a JSON array with one object per example:
\`{"id": "ex07", "verdict": "verifies" | "refused" | "not covered", "functions": [{"name": "...", "verdict": "verifies" | "refused" | "not covered", "first_failing": "expression and obligation, or null"}], "rules": ["definitions and rules of the paper your answer rests on"], "assumed": ["each reading you chose or thing you assumed, with the paper's line; empty if none"], "why": "two or three sentences", "confidence": "high" | "medium" | "low"}\`
The example's verdict is "verifies" when every function verifies, "refused" when at least one is refused, otherwise "not covered".
Then reply with a five-line summary: counts per verdict and the examples you were least sure of.
`;

/** The comments of a TypeScript source, as [start, end) ranges: a scan that
 * skips string, template and regular-expression literals. A `/` starts a
 * regular expression where the previous significant character cannot end
 * an operand, or after a keyword that precedes an expression. */
function commentRanges(text: string): [number, number][] {
  const ranges: [number, number][] = [];
  const templates: number[] = []; // per open `${`, the depth of braces inside it
  let prev = "";
  let i = 0;
  const adjustTemplate = (by: number): void => {
    const top = templates.length - 1;
    if (top >= 0) templates[top] = (templates[top] ?? 0) + by;
  };
  const skipQuoted = (quote: string): void => {
    i++;
    while (i < text.length && text[i] !== quote && text[i] !== "\n") i += text[i] === "\\" ? 2 : 1;
    i++;
  };
  const skipTemplate = (): void => {
    while (i < text.length) {
      if (text[i] === "\\") i += 2;
      else if (text[i] === "`") {
        i++;
        return;
      } else if (text.startsWith("${", i)) {
        templates.push(0);
        i += 2;
        return;
      } else i++;
    }
  };
  const skipRegex = (): void => {
    let inClass = false;
    i++;
    while (i < text.length && text[i] !== "\n") {
      const c = text[i];
      if (c === "\\") i++;
      else if (c === "[") inClass = true;
      else if (c === "]") inClass = false;
      else if (c === "/" && !inClass) break;
      i++;
    }
    i++;
    while (i < text.length && /[a-z]/.test(text[i] ?? "")) i++;
  };
  while (i < text.length) {
    const c = text[i] ?? "";
    if (text.startsWith("//", i)) {
      const end = text.indexOf("\n", i);
      ranges.push([i, end < 0 ? text.length : end]);
      i = end < 0 ? text.length : end;
    } else if (text.startsWith("/*", i)) {
      const end = text.indexOf("*/", i + 2);
      ranges.push([i, end < 0 ? text.length : end + 2]);
      i = end < 0 ? text.length : end + 2;
    } else if (c === "'" || c === '"') {
      skipQuoted(c);
      prev = "a";
    } else if (c === "`") {
      i++;
      skipTemplate();
      prev = "a";
    } else if (c === "/" && (prev === "" || "(,=:[!&|?{};+-*%<>~^".includes(prev) || /\b(return|typeof|case|void|in|of|delete|throw|yield|await)$/.test(prev))) {
      skipRegex();
      prev = "a";
    } else if (c === "{") {
      adjustTemplate(1);
      prev = c;
      i++;
    } else if (c === "}" && templates.length > 0 && templates[templates.length - 1] === 0) {
      templates.pop();
      i++;
      skipTemplate();
      prev = "a";
    } else if (/[A-Za-z0-9_$]/.test(c)) {
      const word = /^[A-Za-z0-9_$]+/.exec(text.slice(i))?.[0] ?? c;
      prev = word;
      i += word.length;
    } else {
      if (c === "}") adjustTemplate(-1);
      if (!/\s/.test(c)) prev = c;
      i++;
    }
  }
  return ranges;
}

const ANNOTATION = /@(requires|ensures|invariant|stable|representation|modifies|pure|param|returns)\b/;

/** A source as a reader sees it: every comment removed but a JSDoc comment
 * carrying an annotation tag, a line left blank by a removal dropped, runs
 * of blank lines reduced to one, and no blank line at either end. */
function stripComments(text: string): string {
  const mark = "\u0001";
  let out = "";
  let at = 0;
  for (const [start, end] of commentRanges(text)) {
    const comment = text.slice(start, end);
    if (comment.startsWith("/**") && ANNOTATION.test(comment)) continue;
    out += text.slice(at, start) + mark;
    at = end;
  }
  out += text.slice(at);
  const lines: string[] = [];
  for (const line of out.split("\n")) {
    if (line.includes(mark) && line.replaceAll(mark, "").trim() === "") continue;
    const kept = line.replaceAll(mark, "").trimEnd();
    if (kept === "" && (lines.length === 0 || lines[lines.length - 1] === "")) continue;
    lines.push(kept);
  }
  while (lines.length > 0 && lines[lines.length - 1] === "") lines.pop();
  return lines.join("\n") + "\n";
}

/** A pseudo-random generator of [0, 1) from a seed (mulberry32). */
function random(seed: number): () => number {
  let state = seed >>> 0;
  return (): number => {
    state = (state + 0x6d2b79f5) >>> 0;
    let t = state;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

function shuffle<T>(items: T[], seed: number): T[] {
  const next = random(seed);
  const out = [...items];
  for (let i = out.length - 1; i > 0; i--) {
    const j = Math.floor(next() * (i + 1));
    const a = out[i];
    const b = out[j];
    if (a === undefined || b === undefined) continue;
    out[i] = b;
    out[j] = a;
  }
  return out;
}

/** The options of a command line: each `--name value`, repeatable, and
 * each flag of `flags` alone. */
function options(args: string[], flags: string[]): Map<string, string[]> {
  const found = new Map<string, string[]>();
  for (let i = 0; i < args.length; i++) {
    const arg = args[i] ?? "";
    if (!arg.startsWith("--")) throw new Error(`unexpected argument ${arg}`);
    const name = arg.slice(2);
    if (flags.includes(name)) {
      found.set(name, ["true"]);
      continue;
    }
    const value = args[++i];
    if (value === undefined) throw new Error(`${arg} needs a value`);
    found.set(name, [...(found.get(name) ?? []), value]);
  }
  return found;
}

function one(found: Map<string, string[]>, name: string): string | undefined {
  const values = found.get(name);
  if (values !== undefined && values.length > 1) throw new Error(`--${name} is given more than once`);
  return values?.[0];
}

function integer(found: Map<string, string[]>, name: string, fallback: number): number {
  const value = one(found, name);
  if (value === undefined) return fallback;
  const n = Number(value);
  if (!Number.isSafeInteger(n) || n < 0) throw new Error(`--${name} takes a non-negative integer, not ${value}`);
  return n;
}

/** The real path of a path that may not exist yet: its nearest existing
 * ancestor's real path, joined with the rest. */
function realPath(path: string): string {
  const absolute = resolve(path);
  if (existsSync(absolute)) return realpathSync(absolute);
  const parent = dirname(absolute);
  return parent === absolute ? absolute : join(realPath(parent), basename(absolute));
}

function prepare(args: string[]): void {
  const found = options(args, []);
  const outOption = one(found, "out");
  if (outOption === undefined) throw new Error("prepare needs --out <dir>");
  const out = realPath(outOption);
  const fromRepository = relative(realpathSync(repository), out);
  if (fromRepository === "" || (!fromRepository.startsWith("..") && !isAbsolute(fromRepository)))
    throw new Error(`${out} is inside the repository; a reader's directory lies outside it`);
  if (existsSync(out) && readdirSync(out).length > 0) throw new Error(`${out} is not empty`);
  const listFile = one(found, "cases");
  const patterns = found.get("pattern") ?? [];
  if (listFile !== undefined && patterns.length > 0) throw new Error("give --cases or --pattern, not both");
  let selected: Case[];
  if (listFile !== undefined) {
    const names = readFileSync(listFile, "utf8").split("\n").map((l) => l.trim()).filter((l) => l !== "" && !l.startsWith("#"));
    selected = names.map((name) => {
      const c = cases.find((k) => k.file === name);
      if (c === undefined) throw new Error(`${listFile}: no case ${name}`);
      return c;
    });
  } else selected = cases.filter((c) => patterns.length === 0 || patterns.some((p) => c.file.includes(p)));
  selected = selected.filter((c, i) => selected.findIndex((k) => k.file === c.file) === i);
  const seed = integer(found, "seed", 1);
  const sample = integer(found, "sample", selected.length);
  const batch = integer(found, "batch", 20);
  if (batch === 0) throw new Error("--batch takes a positive integer");
  const chosen = shuffle(selected, seed).slice(0, sample);
  if (chosen.length === 0) throw new Error("no case is selected");
  const width = Math.max(2, String(chosen.length).length);
  const key: Record<string, KeyEntry> = {};
  mkdirSync(join(out, "examples"), { recursive: true });
  writeFileSync(join(out, "paper.tex"), readFileSync(one(found, "note") ?? defaultNote, "utf8"));
  writeFileSync(join(out, "TASK.md"), TASK);
  const ids = chosen.map((c, i) => {
    const id = `ex${String(i + 1).padStart(width, "0")}`;
    const source = readFileSync(join(repository, "pipeline/examples", `${c.file}.ts`), "utf8");
    writeFileSync(join(out, "examples", `${id}.ts`), stripComments(source));
    key[id] = { case: c.file, kind: c.kind, area: c.area };
    return id;
  });
  let batches = 0;
  for (let i = 0; i < ids.length; i += batch) {
    batches++;
    writeFileSync(join(out, `batch-${batches}.txt`), ids.slice(i, i + batch).join("\n") + "\n");
  }
  writeFileSync(`${out}.key.json`, JSON.stringify(key, null, 1) + "\n");
  process.stdout.write(`${ids.length} examples in ${batches} batches under ${out}; key ${out}.key.json\n`);
}

const isRecord = (v: unknown): v is Record<string, unknown> => typeof v === "object" && v !== null && !Array.isArray(v);
const isVerdict = (v: unknown): v is Verdict => v === "verifies" || v === "refused" || v === "not covered";
const isKind = (v: unknown): v is Kind => v === "positive" || v === "negative" || v === "gap";
const isConfidence = (v: unknown): v is Confidence => v === "high" || v === "medium" || v === "low";
const isStrings = (v: unknown): v is string[] => Array.isArray(v) && v.every((s) => typeof s === "string");

/** Refuses a record with a field outside `fields`. */
function exactFields(record: Record<string, unknown>, fields: string[], where: string): void {
  for (const name of Object.keys(record)) if (!fields.includes(name)) throw new Error(`${where}: unknown field ${name}`);
}

function decodeKey(value: unknown, file: string): Map<string, KeyEntry> {
  if (!isRecord(value)) throw new Error(`${file}: not an object`);
  const key = new Map<string, KeyEntry>();
  for (const [id, entry] of Object.entries(value)) {
    if (!isRecord(entry)) throw new Error(`${file}: ${id}: not an object`);
    exactFields(entry, ["case", "kind", "area"], `${file}: ${id}`);
    const name = entry["case"];
    const kind = entry["kind"];
    const area = entry["area"];
    if (typeof name !== "string") throw new Error(`${file}: ${id}: case is not a string`);
    if (!isKind(kind)) throw new Error(`${file}: ${id}: kind is not positive, negative or gap`);
    if (typeof area !== "string") throw new Error(`${file}: ${id}: area is not a string`);
    key.set(id, { case: name, kind, area });
  }
  return key;
}

function decodeFunction(value: unknown, where: string): FunctionAnswer {
  if (!isRecord(value)) throw new Error(`${where}: a function is not an object`);
  exactFields(value, ["name", "verdict", "first_failing"], where);
  const name = value["name"];
  const verdict = value["verdict"];
  const firstFailing = value["first_failing"];
  if (typeof name !== "string") throw new Error(`${where}: a function's name is not a string`);
  if (!isVerdict(verdict)) throw new Error(`${where}: function ${name}: unknown verdict ${JSON.stringify(verdict)}`);
  if (firstFailing !== null && typeof firstFailing !== "string") throw new Error(`${where}: function ${name}: first_failing is neither a string nor null`);
  return { name, verdict, first_failing: firstFailing };
}

function decodeAnswers(value: unknown, file: string): Answer[] {
  if (!Array.isArray(value)) throw new Error(`${file}: not an array`);
  return value.map((item: unknown, index): Answer => {
    if (!isRecord(item)) throw new Error(`${file}: entry ${index}: not an object`);
    const id = item["id"];
    if (typeof id !== "string") throw new Error(`${file}: entry ${index}: id is not a string`);
    const where = `${file}: ${id}`;
    exactFields(item, ["id", "verdict", "functions", "rules", "assumed", "why", "confidence"], where);
    const { verdict, functions, rules, assumed, why, confidence } = item;
    if (!isVerdict(verdict)) throw new Error(`${where}: unknown verdict ${JSON.stringify(verdict)}`);
    if (!Array.isArray(functions)) throw new Error(`${where}: functions is not an array`);
    if (!isStrings(rules)) throw new Error(`${where}: rules is not a list of strings`);
    if (!isStrings(assumed)) throw new Error(`${where}: assumed is not a list of strings`);
    if (typeof why !== "string") throw new Error(`${where}: why is not a string`);
    if (!isConfidence(confidence)) throw new Error(`${where}: confidence is not high, medium or low`);
    return { id, verdict, functions: functions.map((f: unknown) => decodeFunction(f, where)), rules, assumed, why, confidence };
  });
}

interface Row {
  id: string;
  case: string;
  kind: Kind;
  expected: Verdict;
  reader: Verdict | null;
  result: Result;
  patterns: string[];
  functions: FunctionAnswer[];
}

type Totals = Record<Result, number>;

function totalsOf(rows: Row[]): Totals {
  const totals: Totals = { agree: 0, "not covered": 0, differ: 0, unanswered: 0 };
  for (const row of rows) totals[row.result]++;
  return totals;
}

function totalsLine(totals: Totals, of: number): string {
  return `agree ${totals.agree}, not covered ${totals["not covered"]}, differ ${totals.differ}, unanswered ${totals.unanswered} (of ${of})`;
}

function compare(args: string[]): void {
  const found = options(args, ["json"]);
  const dirOption = one(found, "dir");
  if (dirOption === undefined) throw new Error("compare needs --dir <dir>");
  const dir = resolve(dirOption);
  const keyFile = `${dir}.key.json`;
  const key = decodeKey(JSON.parse(readFileSync(keyFile, "utf8")), keyFile);
  const answers = new Map<string, Answer>();
  for (const name of readdirSync(dir).filter((n) => /^answers-.*\.json$/.test(n)).sort()) {
    const file = join(dir, name);
    const parsed: unknown = JSON.parse(readFileSync(file, "utf8"));
    for (const answer of decodeAnswers(parsed, file)) {
      if (!key.has(answer.id)) throw new Error(`${file}: ${answer.id}: no such example`);
      if (answers.has(answer.id)) throw new Error(`${file}: ${answer.id}: answered twice`);
      answers.set(answer.id, answer);
    }
  }
  const rows: Row[] = [...key.entries()].sort(([a], [b]) => a.localeCompare(b)).map(([id, entry]): Row => {
    const answer = answers.get(id);
    const expected: Verdict = entry.kind === "positive" ? "verifies" : "refused";
    const reader = answer?.verdict ?? null;
    const result: Result = reader === null ? "unanswered" : reader === "not covered" ? "not covered" : reader === expected ? "agree" : "differ";
    const patterns = [...new Set([...entry.area.matchAll(/\bP(\d+)\b/g)].map((m) => `P${m[1]}`))];
    return { id, case: entry.case, kind: entry.kind, expected, reader, result, patterns, functions: answer?.functions ?? [] };
  });
  const totals = totalsOf(rows);
  const patternNames = [...new Set(rows.flatMap((r) => r.patterns))].sort((a, b) => Number(a.slice(1)) - Number(b.slice(1)));
  const perPattern = patternNames.map((p) => {
    const of = rows.filter((r) => r.patterns.includes(p));
    return { pattern: p, of: of.length, totals: totalsOf(of) };
  });
  if (found.has("json")) {
    process.stdout.write(JSON.stringify({ rows, totals, patterns: perPattern }, null, 1) + "\n");
    return;
  }
  const caseWidth = Math.max(4, ...rows.map((r) => r.case.length));
  const lines = [`${"id".padEnd(6)} ${"case".padEnd(caseWidth)} ${"declared".padEnd(8)} ${"reader".padEnd(11)} result`];
  for (const r of rows) lines.push(`${r.id.padEnd(6)} ${r.case.padEnd(caseWidth)} ${r.kind.padEnd(8)} ${(r.reader ?? "-").padEnd(11)} ${r.result}`);
  const notAgreeing = rows.filter((r) => r.result === "differ" || r.result === "not covered");
  if (notAgreeing.length > 0) {
    lines.push("", "Functions of the examples that do not agree:");
    for (const r of notAgreeing) {
      lines.push(`${r.id} ${r.case} (declared ${r.kind}, reader ${r.reader ?? "-"}):`);
      for (const f of r.functions) lines.push(`  ${f.name}: ${f.verdict}${f.first_failing === null ? "" : `, ${f.first_failing}`}`);
    }
  }
  lines.push("", `Totals: ${totalsLine(totals, rows.length)}`);
  for (const p of perPattern) lines.push(`  ${p.pattern}: ${totalsLine(p.totals, p.of)}`);
  process.stdout.write(lines.join("\n") + "\n");
}

if (import.meta.filename === resolve(process.argv[1] ?? "")) {
  const [command, ...rest] = process.argv.slice(2);
  try {
    if (command === "prepare") prepare(rest);
    else if (command === "compare") compare(rest);
    else throw new Error("usage: node dev/paper-readers.mts prepare --out <dir> … | compare --dir <dir> [--json]");
  } catch (error) {
    process.stderr.write(`${error instanceof Error ? error.message : String(error)}\n`);
    process.exitCode = 1;
  }
}
