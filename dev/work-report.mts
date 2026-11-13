// The work of one profiled request, per function and per file
// (docs/drafts/on-demand-processing.md, "Accounting"): how many times each
// kind of work was done on each function and file, its CPU time, and the work
// done more than once, by repetition site.
//   node dev/work-report.mts report <profile directory> [--sources f.ts,…|dir] [--json out.json]
//   node dev/work-report.mts cases <verdicts out>            the pipeline cases with projects
//   node dev/work-report.mts pretext <checkout> <verdicts out> [--files a.ts,…]
//   node dev/work-report.mts census-verdicts <record> <verdicts out>
// A request is profiled with `TSCERT_PROFILE=<profile directory>` in its
// environment: every stage attempt of its processes is appended to the
// directory's `invocations.jsonl`, and each verifier stage's work table,
// executed or replayed, is kept as `work/<attempt>.jsonl`
// (`profileAttempt`, pipeline/stages.mts). The report is a function of that
// directory alone: only executed attempts count as work; a replay is the
// stored result of an execution of an earlier request or of this one.
// `cases`, `pretext` and `census-verdicts` print each file's and each
// unit's verdict, one line each, sorted, to compare two runs.
import { createHash } from "node:crypto";
import { existsSync, mkdtempSync, readdirSync, readFileSync, realpathSync, statSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join, relative, resolve } from "node:path";
import { readInvocationLog, type AttemptRecord } from "../pipeline/stages.mts";

/** One line of a verifier stage's work table (`RequestCli.writeWork`). */
type WorkLine = { kind: string; item: string; count: number; ns: number; selfNs: number };
/** The entries of a map as a record keyed by each key's text. */
function recordOf<K extends string | number, V>(m: Map<K, V>): Record<string, V> {
  const out: Record<string, V> = {};
  for (const [k, v] of m) out[String(k)] = v;
  return out;
}

function readWork(path: string): WorkLine[] {
  if (!existsSync(path)) return [];
  return readFileSync(path, "utf8").split("\n").filter((l) => l !== "").map((l) => {
    const v: unknown = JSON.parse(l);
    if (typeof v !== "object" || v === null || !("kind" in v) || !("item" in v) || !("count" in v) || !("ns" in v) ||
        !("selfNs" in v) || typeof v.kind !== "string" || typeof v.item !== "string" || typeof v.count !== "number" ||
        typeof v.ns !== "number" || typeof v.selfNs !== "number")
      throw Error(`${path}: not a work line: ${l.slice(0, 200)}`);
    return { kind: v.kind, item: v.item, count: v.count, ns: v.ns, selfNs: v.selfNs };
  });
}

/** The repetition sites (the design's section 1, "Repeated processing in one
 * request", and the settled run found by this accounting). */
const sites = {
  roles: "1 requested and imported roles",
  wholeTimeout: "2 whole-file timeout",
  unitFallback: "3 per-unit fallback preparation",
  ordinary: "4 ordinary-contract attempt",
  omission: "5 census omission rounds",
  dependency: "6 census dependency rounds",
  walks: "7 declaration proposal and body extraction",
  init: "8 initialization and returned callables",
  recursive: "9 recursive effect proposals",
  retries: "13 synthesis rounds within one walk",
  restart: "14 preparation at a worker's restart",
  refinement: "11 diagnostic/refinement runs",
  settled: "12 settled run computed twice",
  sameKey: "0 one key executed twice",
} as const;
type Site = (typeof sites)[keyof typeof sites];

/** The class of work a kind belongs to: a file's preparation, a body walk, a
 * check, or an interface/row check; each done once is the ideal. */
function classOf(kind: string): string {
  if (kind.startsWith("walk: ")) return "body walk";
  if (kind === "prepare: claims" || kind === "prepare: file lowering") return "file lowering";
  if (kind === "prepare: freeze" || kind === "prepare: plans over the store") return "freezing";
  if (kind.startsWith("check: ")) return "check";
  return kind;
}

const cpuMs = (r: AttemptRecord): number => "userMs" in r.cpu ? r.cpu.userMs + r.cpu.systemMs : 0;
const ranOf = (r: AttemptRecord): boolean => r.execution === "executed" || r.execution === "timed-out" ||
  r.execution === "failed";

/** An attempt's description: its argument vector and input digests, and,
 * for a part of a worker stage (`invokeWorker`), the part: null for the
 * worker's preparation, a unit's identity, or undefined for any other
 * stage. */
type Manifest = { argv: string[]; inputs: Map<string, string | null>; part: string | null | undefined };
function manifestOf(r: AttemptRecord): Manifest {
  let m = r.manifest;
  let part: string | null | undefined = undefined;
  if (m !== null && typeof m === "object" && !Array.isArray(m) && "worker" in m && "part" in m) {
    const p = new Map<string, unknown>(Object.entries(m)).get("part");
    part = typeof p === "string" ? p : null;
    m = new Map(Object.entries(m)).get("worker") ?? null;
  }
  const argv: string[] = [];
  const inputs = new Map<string, string | null>();
  if (m !== null && typeof m === "object") {
    const fields = new Map<string, unknown>(Object.entries(m));
    const a = fields.get("argv"), i = fields.get("inputs");
    if (Array.isArray(a)) for (const x of a) if (typeof x === "string") argv.push(x);
    if (Array.isArray(i)) for (const p of i)
      if (Array.isArray(p) && typeof p[0] === "string" && (typeof p[1] === "string" || p[1] === null)) inputs.set(p[0], p[1]);
  }
  return { argv, inputs, part };
}

/** An executed verifier attempt with its work. */
type Attempt = { index: number; record: AttemptRecord; work: WorkLine[]; names: string | null; fragment: string | null;
  interfaces: string | null; own: string | null; part: string | null | undefined; cpuNs: number; processNs: number;
  selfNs: number };

/** One occurrence of work: a class of work on an item in one attempt. */
type Occurrence = { attempt: Attempt; cls: string; item: string; kinds: Map<string, WorkLine> };

type Row = { site: Site | "once"; cls: string; item: string; count: number; ns: number };

function report(directory: string, sourceList: string[], jsonOut: string | null): void {
  const records = readInvocationLog(join(directory, "invocations.jsonl"));
  const labels = new Map<string, string>();
  for (const s of sourceList)
    labels.set(createHash("sha256").update(readFileSync(s)).digest("hex").slice(0, 12), relative(process.cwd(), s));
  const label = (item: string): string => {
    const [file, unit] = item.split("#");
    return `${labels.get(file ?? "") ?? file}${unit === undefined ? "" : `#${unit}`}`;
  };
  const attempts: Attempt[] = [];
  const stageCpu = new Map<string, { executed: number; replayed: number; cpuMs: number; timedOut: number }>();
  let timedOutWholeMs = 0, timedOutUnitMs = 0, totalMs = 0;
  /** The worker processes started for each fragment: its preparations executed. */
  const workerStarts = new Map<string, number>();
  for (const [index, r] of records.entries()) {
    const s = stageCpu.get(r.stage) ?? { executed: 0, replayed: 0, cpuMs: 0, timedOut: 0 };
    stageCpu.set(r.stage, s);
    if (!ranOf(r)) { s.replayed++; continue; }
    s.executed++;
    s.cpuMs += cpuMs(r);
    totalMs += cpuMs(r);
    const m = manifestOf(r);
    const names = r.stage === "pass" ? (m.argv.at(-1) ?? null) : null;
    if (r.execution === "timed-out") {
      s.timedOut++;
      if (r.stage === "pass" && names === "" && m.part === undefined) timedOutWholeMs += cpuMs(r);
      else timedOutUnitMs += cpuMs(r);
      continue;
    }
    const work = readWork(join(directory, "work", `${r.attempt}.jsonl`));
    if (work.length === 0) continue;
    const process = work.find((w) => w.kind === "process");
    const own = work.find((w) => w.kind === "prepare: importer plans")?.item ?? null;
    if (m.part === null) workerStarts.set(m.inputs.get("fragment.json") ?? "", (workerStarts.get(m.inputs.get("fragment.json") ?? "") ?? 0) + 1);
    attempts.push({ index, record: r, work, names, fragment: m.inputs.get("fragment.json") ?? null,
      interfaces: m.inputs.get("interfaces.json") ?? null, own, part: m.part,
      cpuNs: cpuMs(r) * 1e6, processNs: process?.ns ?? 0,
      selfNs: work.filter((w) => w.kind !== "process").reduce((a, w) => a + w.selfNs, 0) });
  }
  // A worker's unit parts are of the file whose preparation is the
  // worker's: its own file's item, from the preparation of the same fragment.
  const ownOf = new Map<string, string>();
  for (const a of attempts) if (a.own !== null && a.fragment !== null) ownOf.set(a.fragment, a.own);
  for (const a of attempts) if (a.own === null && a.part !== undefined && a.fragment !== null) a.own = ownOf.get(a.fragment) ?? null;
  // Each attempt's occurrences: a class of work on an item, its kinds.
  const occurrences = new Map<string, Occurrence[]>();
  for (const a of attempts) {
    const here = new Map<string, Occurrence>();
    for (const w of a.work) {
      if (w.kind === "process") continue;
      const cls = classOf(w.kind);
      const key = `${cls}\t${w.item}`;
      const o = here.get(key) ?? { attempt: a, cls, item: w.item, kinds: new Map<string, WorkLine>() };
      o.kinds.set(w.kind, w);
      here.set(key, o);
    }
    for (const [key, o] of here) occurrences.set(key, [...(occurrences.get(key) ?? []), o]);
  }
  // An attempt's CPU outside its recorded work (reading, decoding,
  // encoding, starting) is shared among its work in proportion.
  const scale = (a: Attempt): number => a.selfNs > 0 ? Math.max(1, a.cpuNs / a.selfNs) : 1;
  const rows: Row[] = [];
  const push = (site: Site | "once", o: Occurrence, count: number, ns: number): void => {
    if (count > 0 || ns > 0) rows.push({ site, cls: o.cls, item: o.item, count, ns: ns * scale(o.attempt) });
  };
  /** Which site a second attempt's occurrence repeats the first's at. */
  const across = (first: Attempt, other: Attempt): Site => {
    const stageA = first.record.stage, stageB = other.record.stage;
    if (stageA !== stageB || stageA !== "pass") return sites.roles;
    if (first.fragment !== other.fragment) return sites.omission;
    if (first.names !== other.names) return first.names !== "" && other.names !== "" || attemptsTimedOut.has(other.fragment ?? "")
      ? sites.unitFallback : sites.dependency;
    if (first.interfaces !== other.interfaces) return sites.ordinary;
    if (first.part === null && other.part === null) return sites.restart;
    return sites.sameKey;
  };
  // The fragments whose whole-file pass timed out: their unit stages are
  // the fallback.
  const attemptsTimedOut = new Set<string>();
  for (const r of records)
    if (r.stage === "pass" && r.execution === "timed-out" && manifestOf(r).argv.at(-1) === "")
      attemptsTimedOut.add(manifestOf(r).inputs.get("fragment.json") ?? "");
  for (const [, list] of occurrences) {
    // The occurrence that counts as the processing: the first in the item's
    // own file's pass, else the first.
    const ownFile = (o: Occurrence): boolean => o.attempt.record.stage === "pass" &&
      o.attempt.own !== null && o.item.startsWith(o.attempt.own);
    const canonical = list.find(ownFile) ?? list[0];
    for (const o of list) {
      const total = [...o.kinds.values()];
      const ns = (k: string): number => o.kinds.get(k)?.ns ?? 0;
      const count = (k: string): number => o.kinds.get(k)?.count ?? 0;
      const selfSum = total.reduce((a, w) => a + w.selfNs, 0);
      if (o !== canonical) {
        push(across(canonical.attempt, o.attempt), o, total.reduce((a, w) => a + w.count, 0), selfSum);
        continue;
      }
      if (o.cls === "check") {
        // Member runs: the first is the processing; a rerun follows each
        // diagnosing walk; one more is the settled run computed twice
        // (`settleInferred`); main graph runs beyond the member runs are
        // regional checks beside a run.
        const c = count("check: member run"), d = count("check: diagnosing walk"), m = count("check: main graph run");
        const perRun = c > 0 ? ns("check: member run") / c : 0;
        const reruns = Math.min(d, Math.max(0, c - 1));
        const twice = Math.max(0, c - 1 - reruns);
        const regional = Math.max(0, m - c);
        const regionalNs = m > 0 ? regional * ns("check: main graph run") / m : 0;
        push(sites.settled, o, twice, twice * perRun);
        push(sites.refinement, o, reruns + d + regional, reruns * perRun + ns("check: diagnosing walk") + regionalNs);
        push("once", o, c > 0 ? 1 : count("check: group"), Math.max(0, selfSum - (twice + reruns) * perRun -
          ns("check: diagnosing walk") - regionalNs));
        continue;
      }
      if (o.cls === "body walk") {
        // One walk of a body is the processing: the proposal walk where
        // there is one; the returned-callable round, recursive walks and
        // the extraction's walks are repetitions.
        // A walk's own rounds over the body after its first (an evolving
        // binding's growth, offered rows) are counted apart, nested in it.
        let first = true;
        for (const w of total) {
          if (w.kind === "walk: growth round" || w.kind === "walk: offers round") {
            push(sites.retries, o, w.count, w.selfNs);
            continue;
          }
          const site = w.kind === "walk: proposal, returned-callable round" ? sites.init
            : w.kind === "walk: proposal, recursive again" ? sites.recursive
            : o.item.endsWith("#init") ? sites.init : sites.walks;
          const once = first && (w.kind === "walk: proposal" || !o.kinds.has("walk: proposal"));
          if (once) {
            first = false;
            push("once", o, 1, w.selfNs / w.count);
            push(site, o, w.count - 1, w.selfNs * (w.count - 1) / w.count);
          } else push(site, o, w.count, w.selfNs);
        }
        continue;
      }
      // Any other work done more than once in one attempt: initialization
      // typing and the rest.
      for (const w of total) {
        push("once", o, 1, w.selfNs / w.count);
        push(o.cls === "prepare: initialization typing" ? sites.init : sites.refinement, o, w.count - 1,
          w.selfNs * (w.count - 1) / w.count);
      }
    }
  }
  // Signature obligations: an overloaded function's units are its
  // signatures, each its own item (`name~k`, `Front.lexicalId`), checked once.
  const signatures = new Set<string>();
  for (const [, list] of occurrences) if (list[0].cls === "check" && /#[^#]+~\d+$/.test(list[0].item)) signatures.add(list[0].item);
  // The parses: a file's lowering by TypeScript, as itself (`parse`) and as
  // a module an importer reads (`module`, nested in the importer's parse),
  // each keyed by its path; the paths' digests are told by `--sources`.
  const digest = (text: string): string => createHash("sha256").update(text).digest("hex");
  const pathOf = new Map<string, string>();
  for (const f of sourceList) {
    const real = realpathSync(f);
    for (const v of [resolve(f), real, real.replace(/^\/private\//, "/")]) pathOf.set(digest(v), real);
  }
  const lowered = new Map<string, AttemptRecord>();
  let parseRepeated = { count: 0, ms: 0 }, parseOmitted = { count: 0, ms: 0 };
  const loweringOf = (r: AttemptRecord): string | undefined => {
    const i = manifestOf(r).inputs;
    return pathOf.get((r.stage === "parse" ? i.get("resolution") : i.get("module")) ?? "");
  };
  const lowerings = records.filter((r) => ranOf(r) && (r.stage === "parse" || r.stage === "module"));
  // The file's own parse is its lowering, else its first module lowering.
  for (const r of [...lowerings.filter((r) => r.stage === "parse"), ...lowerings.filter((r) => r.stage === "module")]) {
    const i = manifestOf(r).inputs;
    const file = loweringOf(r);
    if (file === undefined) continue;
    const first = lowered.get(file);
    if (first === undefined) { lowered.set(file, r); continue; }
    const omittedDiffers = first.stage === "parse" && r.stage === "parse" &&
      manifestOf(first).inputs.get("omitted") !== i.get("omitted");
    const into = omittedDiffers ? parseOmitted : parseRepeated;
    into.count++;
    into.ms += cpuMs(r);
  }
  // Totals.
  const attributedMs = rows.reduce((a, r) => a + r.ns, 0) / 1e6;
  const repeated = rows.filter((r) => r.site !== "once");
  const repeatedMs = repeated.reduce((a, r) => a + r.ns, 0) / 1e6 + timedOutWholeMs + parseRepeated.ms + parseOmitted.ms;
  const bySite = new Map<string, { count: number; ms: number }>();
  for (const r of repeated) {
    const s = bySite.get(r.site) ?? { count: 0, ms: 0 };
    s.count += r.count;
    s.ms += r.ns / 1e6;
    bySite.set(r.site, s);
  }
  const addSite = (site: string, x: { count: number; ms: number }): void => {
    if (x.count === 0) return;
    const s = bySite.get(site) ?? { count: 0, ms: 0 };
    bySite.set(site, { count: s.count + x.count, ms: s.ms + x.ms });
  };
  addSite(`${sites.roles} (parse level)`, parseRepeated);
  addSite(`${sites.omission} (parse level)`, parseOmitted);
  if (timedOutWholeMs > 0) bySite.set(sites.wholeTimeout, { count: [...records].filter((r) => r.stage === "pass" &&
    r.execution === "timed-out" && manifestOf(r).argv.at(-1) === "").length, ms: timedOutWholeMs });
  // Per function: the attempts that worked on it and its traversals.
  // (a worker's pieces one stage: its preparations and its units' checks)
  const stageOf = (a: Attempt): string => a.part === undefined ? String(a.index)
    : `worker ${a.fragment ?? ""} ${a.interfaces ?? ""} ${a.names ?? ""}`;
  const fns = new Map<string, { attempts: Set<string>; traversals: number; ms: number; repeatedMs: number }>();
  for (const [, list] of occurrences) for (const o of list) {
    if (!o.item.includes("#")) continue;
    const f = fns.get(o.item) ?? { attempts: new Set<string>(), traversals: 0, ms: 0, repeatedMs: 0 };
    f.attempts.add(stageOf(o.attempt));
    for (const [k, w] of o.kinds) if (k.startsWith("walk: ") || k === "check: member run" || k === "check: diagnosing walk")
      f.traversals += w.count;
    fns.set(o.item, f);
  }
  for (const r of rows) {
    const f = fns.get(r.item);
    if (!f) continue;
    f.ms += r.ns / 1e6;
    if (r.site !== "once") f.repeatedMs += r.ns / 1e6;
  }
  const units = [...fns.entries()];
  const attemptsPer = units.map(([, f]) => f.attempts.size);
  const traversalsPer = units.map(([, f]) => f.traversals);
  const mean = (xs: number[]): number => xs.length ? xs.reduce((a, b) => a + b, 0) / xs.length : 0;
  const s = (ms: number): string => (ms / 1000).toFixed(1);
  const out: string[] = [];
  out.push(`stage CPU executed: ${s(totalMs)} s over ${[...stageCpu.values()].reduce((a, x) => a + x.executed, 0)} attempts ` +
    `(${[...stageCpu.values()].reduce((a, x) => a + x.replayed, 0)} replayed)`);
  for (const [stage, x] of [...stageCpu].sort((a, b) => b[1].cpuMs - a[1].cpuMs))
    out.push(`  ${stage}: ${s(x.cpuMs)} s, ${x.executed} executed${x.timedOut ? ` (${x.timedOut} over their limit)` : ""}, ${x.replayed} replayed`);
  out.push(`work attributed to functions and files: ${s(attributedMs)} s; whole-file passes over their limit: ${s(timedOutWholeMs)} s; ` +
    `unit stages over their limit: ${s(timedOutUnitMs)} s`);
  out.push(`work done more than once: ${s(repeatedMs)} s, ${(100 * repeatedMs / Math.max(1, totalMs)).toFixed(1)}% of stage CPU`);
  for (const [site, x] of [...bySite].sort((a, b) => b[1].ms - a[1].ms))
    out.push(`  ${site}: ${s(x.ms)} s (${(100 * x.ms / Math.max(1, totalMs)).toFixed(1)}%), ${x.count} times`);
  out.push(`signature obligations of overloaded functions checked: ${signatures.size}`);
  const starts = [...workerStarts.values()];
  if (starts.length > 0)
    out.push(`file workers: ${starts.length} files, ${starts.reduce((a, b) => a + b, 0)} worker starts, max ${Math.max(...starts)} per file`);
  out.push(`functions and initializations worked on: ${units.length}; stages working on each: max ${Math.max(0, ...attemptsPer)}, ` +
    `mean ${mean(attemptsPer).toFixed(2)}; body traversals (walks and runs) of each: max ${Math.max(0, ...traversalsPer)}, ` +
    `mean ${mean(traversalsPer).toFixed(2)}`);
  const byClass = new Map<string, { once: number; repeated: number }>();
  for (const r of rows) {
    const c = byClass.get(r.cls) ?? { once: 0, repeated: 0 };
    if (r.site === "once") c.once += r.ns / 1e6; else c.repeated += r.ns / 1e6;
    byClass.set(r.cls, c);
  }
  out.push("by class of work (once / more than once, s):");
  for (const [c, x] of [...byClass].sort((a, b) => (b[1].once + b[1].repeated) - (a[1].once + a[1].repeated)))
    out.push(`  ${c}: ${s(x.once)} / ${s(x.repeated)}`);
  out.push("functions with the most work done more than once (s repeated of s, stages, traversals):");
  for (const [item, f] of units.sort((a, b) => b[1].repeatedMs - a[1].repeatedMs).slice(0, 15))
    out.push(`  ${label(item)}: ${s(f.repeatedMs)} of ${s(f.ms)}, ${f.attempts.size}, ${f.traversals}`);
  process.stdout.write(out.join("\n") + "\n");
  if (jsonOut !== null)
    writeFileSync(jsonOut, JSON.stringify({ totalMs, attributedMs, repeatedMs, timedOutWholeMs, timedOutUnitMs,
      workerStarts: recordOf(workerStarts),
      sites: recordOf(bySite), byClass: recordOf(byClass),
      stages: recordOf(stageCpu),
      functions: recordOf(new Map(units.map(([item, f]) => [label(item),
        { attempts: f.attempts.size, traversals: f.traversals, ms: f.ms, repeatedMs: f.repeatedMs }] as const))) }, null, 1) + "\n");
}

/** The sources a `--sources` value names: files, or every `.ts`/`.mts` file of a directory. */
function sourcesOf(value: string | null): string[] {
  if (value === null) return [];
  return value.split(",").flatMap((p) => statSync(p).isDirectory()
    ? readdirSync(p).filter((n) => /\.m?ts$/.test(n)).map((n) => join(p, n)) : [p]);
}

/** A unit's verdict line: its file, unit, status and its detail's first line. */
type Verdicted = { status: string; phase?: string; detail?: string;
  units?: { unit: string; status: string; detail: string }[] | null };
function verdictLines(file: string, o: Verdicted): string[] {
  const first = (d: string | undefined): string =>
    (d ?? "").split("\n").find((l) => l !== "" && !l.startsWith("obligation-diagnostic: "))?.slice(0, 300) ?? "";
  return [`${file}\t${o.status}\t${o.phase ?? ""}\t${o.status === "verified" ? "" : first(o.detail)}`,
    ...(o.units ?? []).map((u) => `${file}#${u.unit}\t${u.status}\t\t${first(u.detail)}`)];
}

const [command, ...rest] = process.argv.slice(2);
const option = (name: string): string | null => {
  const at = rest.indexOf(name);
  if (at < 0) return null;
  const v = rest[at + 1] ?? null;
  rest.splice(at, 2);
  return v;
};
if (command === "report") {
  const sources = sourcesOf(option("--sources"));
  const json = option("--json");
  if (rest.length !== 1) throw Error("usage: report <profile directory> [--sources …] [--json out]");
  report(resolve(rest[0]), sources, json);
} else if (command === "cases") {
  const { cases } = await import("../pipeline/cases.mts");
  const { runCase, pooled } = await import("../pipeline/run-cases.mts");
  const { linkFixtures } = await import("../pipeline/fixture-links.mts");
  const { startEviction } = await import("../pipeline/stages.mts");
  if (rest.length !== 1) throw Error("usage: cases <verdicts out>");
  startEviction();
  linkFixtures();
  const selected = cases.filter((c) => c.project !== undefined);
  const started = performance.now();
  const settled = await pooled(selected, runCase);
  const lines = selected.flatMap((c, i) => {
    const r = settled[i];
    return r.status === "fulfilled" ? verdictLines(c.file, r.value) : [`${c.file}\tfailed\t\t${String(r.reason).split("\n")[0]}`];
  });
  writeFileSync(rest[0], lines.sort().join("\n") + "\n");
  process.stdout.write(`${selected.length} cases with projects, ${((performance.now() - started) / 1000).toFixed(1)} s\n`);
} else if (command === "pretext") {
  const { checkApart } = await import("../pipeline/verify-source.mts");
  const { startEviction } = await import("../pipeline/stages.mts");
  const files = option("--files");
  if (rest.length !== 2) throw Error("usage: pretext <checkout> <verdicts out> [--files a.ts,…]");
  startEviction();
  const root = resolve(rest[0]);
  const project = mkdtempSync(join(tmpdir(), "work-report-pretext-"));
  writeFileSync(join(project, "tsconfig.json"), JSON.stringify({ extends: join(root, "tsconfig.json"),
    compilerOptions: { types: [] }, include: [join(root, "src/**/*.ts")], exclude: [join(root, "src/layout.test.ts")] }));
  const chosen = files?.split(",") ?? readdirSync(join(root, "src"))
    .filter((f) => f.endsWith(".ts") && !f.endsWith(".d.ts") && !f.includes(".test.")).sort();
  const started = performance.now();
  const lines = (await Promise.all(chosen.map(async (f) => {
    using r = await checkApart(join(root, "src", f), project, false, undefined, true, { omitted: [], select: null });
    return verdictLines(f, r);
  }))).flat();
  writeFileSync(rest[1], lines.sort().join("\n") + "\n");
  process.stdout.write(`${chosen.length} pretext files, ${((performance.now() - started) / 1000).toFixed(1)} s\n`);
} else if (command === "census-verdicts") {
  if (rest.length !== 2) throw Error("usage: census-verdicts <record> <verdicts out>");
  const record: unknown = JSON.parse(readFileSync(rest[0], "utf8"));
  const files = typeof record === "object" && record !== null && "files" in record && Array.isArray(record.files)
    ? record.files : [];
  const lines: string[] = [];
  for (const f of files) {
    if (typeof f !== "object" || f === null || !("file" in f) || typeof f.file !== "string") continue;
    const units = "units" in f && Array.isArray(f.units) ? f.units : [];
    for (const u of units)
      if (typeof u === "object" && u !== null && "unit" in u && "status" in u && "detail" in u &&
          typeof u.unit === "string" && typeof u.status === "string" && typeof u.detail === "string")
        lines.push(`${f.file}#${u.unit}\t${u.status}\t\t${u.detail.split("\n").find((l: string) => l !== "" &&
          !l.startsWith("obligation-diagnostic: "))?.slice(0, 300) ?? ""}`);
  }
  writeFileSync(rest[1], lines.sort().join("\n") + "\n");
} else {
  process.stderr.write("usage: node dev/work-report.mts report|cases|pretext|census-verdicts …\n");
  process.exit(2);
}
