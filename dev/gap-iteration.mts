/* One iteration of gap work (the gap-round skill, .claude/skills/gap-round/)
 * from the command line, each role played by a model given as a parameter:
 *
 *   node dev/gap-iteration.mts rank   --cases N [--census <record>] [--previous <record>] [--causes <file>] [--run <dir>]
 *   node dev/gap-iteration.mts work   --run <dir> [--parallel 5]
 *   node dev/gap-iteration.mts finish --run <dir>
 *   node dev/gap-iteration.mts all    --cases N [...]        # rank, work, finish
 *   common: [--driver sol] [--agent sol] [--reviewer astra] [--codex-stop 85]
 *
 * `--causes <file>` gives the round's causes instead of ranking them: a
 * JSON list of {"reason", "statements", "functions"} and optionally "case",
 * worked in its order; the driver finds each cause's sites in the census,
 * adds the case each lacks, and ranks nothing.
 *
 * `rank` takes the census of main (the given record when its commit has
 * main's code, otherwise a new one) and its refusals (`census.mts
 * refusals`), and has the driver confirm their reasons, add the case each
 * reason lacks and write the top N open cases as `ranking.json` (the
 * skill's steps 1-3); that record is the census the iteration's movement is
 * measured from, unless `--previous` names another. `work` closes the cases,
 * at most `--parallel` at a time (step 4). `finish` runs main's suites and
 * the census, records the movement in WORK.md, rebuilds the gap-priorities
 * deck from the new census's refusals, and writes `report.md`
 * (steps 5, 6 and the report). Nothing is pushed.
 *
 * Every change is a task: an author's run in its own worktree, on branch
 * `gap/<task>` from main, then, by the script: main integrated by rebase,
 * the task's gates (`make build`, `make suite`, `make test`, or the docs
 * checks), the reviewer's review of `git diff main...` until it has no
 * blocking finding (the reviewer implementing them, two rounds at most),
 * and a fast-forward merge into main, one at a time. A gate or review left
 * failing makes the task incomplete, with its reason; it closes no case.
 * Authors write each commit record using only the glossary's terms or terms
 * the record explains.
 *
 * Models: `sol` (codex gpt-6.1-sol), `astra` (codex gpt-6-astra) or
 * `codex:<id>`. An author runs `codex exec --approve-for-me`: its commands
 * run in codex's sandbox, without network, writing its worktree, the run's
 * `work/` directory and the stage and Dune caches; a command that needs more
 * (the pipeline's own sandbox-exec, a commit) runs outside it on codex's
 * automatic approval. Reviews and the report run read-only.
 * The script runs every gate, commit rewrite and merge itself, with the
 * owner's permissions, over the authors' code. Before each codex run the
 * newest codex session's usage is read; at `--codex-stop` percent of either
 * window, or on a usage-limit failure, the command stops, and repeating it
 * resumes from `state.json`. One command runs at a time. */
import { execFileSync, spawn } from "node:child_process";
import { appendFileSync, existsSync, mkdirSync, readdirSync, readFileSync, renameSync, rmSync, statSync, statfsSync,
  writeFileSync } from "node:fs";
import { homedir, tmpdir } from "node:os";
import { join, resolve } from "node:path";
import { setTimeout as sleep } from "node:timers/promises";

const repository = resolve(import.meta.dirname, "..");
const lockRoot = join(tmpdir(), "tscert-gap");

// ---------------------------------------------------------------- options

type Options = { driver: string; agent: string; reviewer: string; parallel: number; codexStop: number; cases: number;
  census: string | null; previous: string | null; causes: string | null; run: string | null };

function option(args: string[], name: string): string | null {
  const at = args.indexOf(name);
  if (at < 0) return null;
  const value = args[at + 1];
  if (value === undefined) throw Error(`${name} needs a value`);
  args.splice(at, 2);
  return value;
}

/** A role's codex model: an alias or `codex:<id>`. */
function model(name: string): string {
  const aliases: { [alias: string]: string } = { sol: "gpt-6.1-sol", astra: "gpt-6-astra" };
  const alias = aliases[name];
  if (alias !== undefined) return alias;
  if (name.startsWith("codex:")) return name.slice("codex:".length);
  throw Error(`model ${name}: this command runs codex roles (sol, astra, codex:<id>)`);
}

function options(args: string[]): Options {
  const number = (name: string, fallback: number): number => {
    const text = option(args, name);
    const value = text === null ? fallback : Number(text);
    if (!Number.isInteger(value) || value < 1) throw Error(`${name} needs a positive integer`);
    return value;
  };
  const parsed: Options = {
    driver: model(option(args, "--driver") ?? "sol"), agent: model(option(args, "--agent") ?? "sol"),
    reviewer: model(option(args, "--reviewer") ?? "astra"), parallel: number("--parallel", 5),
    codexStop: number("--codex-stop", 85), cases: number("--cases", 5), census: option(args, "--census"),
    previous: option(args, "--previous"), causes: option(args, "--causes"), run: option(args, "--run"),
  };
  if (parsed.parallel > 5) throw Error("--parallel is at most 5");
  if (args.length) throw Error(`unknown arguments: ${args.join(" ")}`);
  return parsed;
}

// ---------------------------------------------------------------- state

type Kind = "repros" | "case" | "row" | "deck";
type Status = "pending" | "merged" | "incomplete";
/** A task: one branch of work and how far it went. `gated` is the tree
 * whose gates passed, `reviewed` the patch id the review approved. */
type Task = { id: string; kind: Kind; status: Status; note: string; reason: string; sites: string[]; statements: number;
  functions: number; authored: boolean; gated: string; reviewed: string };
type State = { repository: string; base: string; census: string; previous: string; verified: string; tasks: Task[] };

const isStrings = (v: unknown): v is string[] => Array.isArray(v) && v.every((s) => typeof s === "string");

function decodeTask(v: unknown): Task {
  if (!v || typeof v !== "object") throw Error("state: a task is not an object");
  const kinds: unknown[] = ["repros", "case", "row", "deck"], statuses: unknown[] = ["pending", "merged", "incomplete"];
  if (!("id" in v && typeof v.id === "string" && "kind" in v && kinds.includes(v.kind) && "status" in v &&
    statuses.includes(v.status) && "note" in v && typeof v.note === "string" && "reason" in v && typeof v.reason === "string" &&
    "sites" in v && isStrings(v.sites) && "statements" in v && typeof v.statements === "number" && "functions" in v &&
    typeof v.functions === "number" && "authored" in v && typeof v.authored === "boolean" && "gated" in v &&
    typeof v.gated === "string" && "reviewed" in v && typeof v.reviewed === "string"))
    throw Error("state: a task lacks a field");
  return v as Task; // asserted: every field of Task checked above
}

function readState(run: string): State {
  const v: unknown = JSON.parse(readFileSync(join(run, "state.json"), "utf8"));
  if (!(v && typeof v === "object" && "repository" in v && typeof v.repository === "string" && "base" in v &&
    typeof v.base === "string" && "census" in v && typeof v.census === "string" && "previous" in v &&
    typeof v.previous === "string" && "verified" in v && typeof v.verified === "string" && "tasks" in v &&
    Array.isArray(v.tasks)))
    throw Error(`${run}/state.json lacks a field`);
  if (v.repository !== repository) throw Error(`${run} belongs to ${v.repository}`);
  return { repository: v.repository, base: v.base, census: v.census, previous: v.previous, verified: v.verified,
    tasks: v.tasks.map(decodeTask) };
}

function writeState(run: string, state: State): void {
  writeFileSync(join(run, "state.json.tmp"), JSON.stringify(state, null, 1) + "\n");
  renameSync(join(run, "state.json.tmp"), join(run, "state.json"));
}

// ---------------------------------------------------------------- processes

/** Stops the command, resumably: codex's usage reached its stop. */
class Paused extends Error {}

/** A command's exit status and the last 64 KiB of its output, which is
 * appended to `log` as it runs. */
function exec(command: string, args: string[], o: { cwd: string; log: string; env?: { [name: string]: string } }):
  Promise<{ status: number; output: string }> {
  return new Promise((done, fail) => {
    appendFileSync(o.log, `\n$ ${command} ${args.map((a) => a.length > 200 ? a.slice(0, 200) + "…" : a).join(" ")}\n`);
    const child = spawn(command, args, { cwd: o.cwd, env: { ...process.env, ...o.env }, stdio: ["ignore", "pipe", "pipe"] });
    child.stdout.setEncoding("utf8");
    child.stderr.setEncoding("utf8");
    let output = "";
    const take = (chunk: unknown): void => {
      const text = String(chunk);
      appendFileSync(o.log, text);
      output = (output + text).slice(-65536);
    };
    child.stdout.on("data", take);
    child.stderr.on("data", take);
    child.on("error", fail);
    child.on("close", (code) => done({ status: code ?? 1, output }));
  });
}

function git(cwd: string, ...args: string[]): string {
  return execFileSync("git", ["-C", cwd, ...args], { encoding: "utf8", stdio: ["ignore", "pipe", "pipe"] }).trim();
}
function gitOk(cwd: string, ...args: string[]): boolean {
  try { git(cwd, ...args); return true; } catch { return false; }
}

/** Runs `work` holding the lock directory `lock`, waiting for it. */
async function locked<T>(lock: string, work: () => Promise<T>): Promise<T> {
  for (;;) {
    try { mkdirSync(lock); break; } catch (e) {
      if (!(e instanceof Error && "code" in e && e.code === "EEXIST")) throw e;
      await sleep(20_000);
    }
  }
  try { return await work(); } finally { rmSync(lock, { recursive: true, force: true }); }
}

/** One promise after another: the merges into main. */
let merging: Promise<unknown> = Promise.resolve();
function serially<T>(work: () => Promise<T>): Promise<T> {
  const next = merging.then(work);
  merging = next.catch(() => undefined);
  return next;
}

/** The highest used percentage of either window in the newest codex
 * session's last usage line, or null when none is found. */
function codexUsage(): number | null {
  const newest = (dir: string): string | null => {
    if (!existsSync(dir)) return null;
    const names = readdirSync(dir).sort().reverse();
    for (const name of names) {
      const path = join(dir, name);
      if (statSync(path).isDirectory()) { const found = newest(path); if (found) return found; }
    }
    const files = names.filter((n) => n.endsWith(".jsonl")).map((n) => join(dir, n));
    return files.sort((a, b) => statSync(b).mtimeMs - statSync(a).mtimeMs)[0] ?? null;
  };
  const file = newest(join(homedir(), ".codex", "sessions"));
  if (!file) return null;
  const line = readFileSync(file, "utf8").split("\n").filter((l) => l.includes('"rate_limits"')).at(-1);
  if (!line) return null;
  const used = [...line.matchAll(/"(?:primary|secondary)":\{"used_percent":([0-9.]+)/g)].map((m) => Number(m[1]));
  return used.length ? Math.max(...used) : null;
}

type Run = { run: string; o: Options; state: State };

/** A codex run's final message. An author (`write`) runs in codex's sandbox
 * with automatic approval of what needs more; every other run is read-only. */
async function codex(r: Run, c: { model: string; cwd: string; prompt: string; out: string; log: string; write: boolean;
  schema?: object }): Promise<string> {
  const used = codexUsage();
  if (used !== null && used >= r.o.codexStop) throw new Paused(`codex usage at ${used}% (stop at ${r.o.codexStop}%)`);
  const tmp = join(r.run, "work", "tmp");
  mkdirSync(tmp, { recursive: true });
  const args = ["exec", "-m", c.model, "--skip-git-repo-check", "-C", c.cwd, "-o", c.out];
  if (c.write) {
    const roots = [join(r.run, "work"), join(homedir(), ".cache", "tscert"), join(homedir(), ".cache", "dune")];
    args.push("--approve-for-me", "-c", "sandbox_workspace_write.exclude_slash_tmp=true",
      "-c", `sandbox_workspace_write.writable_roots=${JSON.stringify(roots)}`);
  } else args.push("-s", "read-only");
  if (c.schema) {
    const schema = c.out + ".schema.json";
    writeFileSync(schema, JSON.stringify(c.schema));
    args.push("--output-schema", schema);
  }
  rmSync(c.out, { force: true });
  const ran = await exec("codex", [...args, c.prompt], { cwd: c.cwd, log: c.log, env: { TMPDIR: tmp } });
  if (/usage limit|rate limit/i.test(ran.output) && ran.status !== 0) throw new Paused(`codex usage limit (${c.log})`);
  if (ran.status !== 0 || !existsSync(c.out)) throw Error(`codex ${c.model} failed, status ${ran.status} (${c.log})`);
  return readFileSync(c.out, "utf8");
}

/** A markdown file's section under `heading`, to the next heading of its
 * level or above. */
function section(file: string, heading: string): string {
  const lines = readFileSync(join(repository, file), "utf8").split("\n");
  const at = lines.findIndex((l) => l.startsWith("#") && l.includes(heading));
  if (at < 0) throw Error(`${file} has no section ${heading}`);
  const level = /^#+/.exec(lines[at] ?? "")?.[0].length ?? 1;
  const end = lines.findIndex((l, i) => i > at && /^#+ /.test(l) && (/^#+/.exec(l)?.[0].length ?? 9) <= level);
  return lines.slice(at, end < 0 ? undefined : end).join("\n");
}

// ---------------------------------------------------------------- tasks

const taskDir = (r: Run, t: Task): string => join(r.run, "tasks", t.id);
const treeOf = (r: Run, t: Task): string => join(r.run, "trees", t.id);
const work = (r: Run): string => join(r.run, "work");
const branchOf = (t: Task): string => `gap/${t.id}`;
const heavy = (r: Run): string => join(work(r), "heavy.lock");
const logOf = (r: Run, t: Task): string => join(taskDir(r, t), "log.txt");

function save(r: Run): void { writeState(r.run, r.state); }
function close(r: Run, t: Task, status: Status, note: string): void {
  t.status = status;
  t.note = note;
  save(r);
  process.stderr.write(`${t.id}: ${status}${note ? ` (${note})` : ""}\n`);
}

/** The task's worktree on its branch from main, with the main checkout's
 * Lake cache, node_modules and a build. */
async function setUp(r: Run, t: Task): Promise<void> {
  const tree = treeOf(r, t);
  mkdirSync(taskDir(r, t), { recursive: true });
  if (existsSync(tree)) return;
  mkdirSync(join(r.run, "trees"), { recursive: true });
  if (gitOk(repository, "rev-parse", "--verify", "-q", `refs/heads/${branchOf(t)}`))
    git(repository, "worktree", "add", "-q", tree, branchOf(t));
  else git(repository, "worktree", "add", "-q", "-b", branchOf(t), tree, "main");
  execFileSync("cp", ["-c", "-R", join(repository, "lean", ".lake"), join(tree, "lean", ".lake")]);
  rmSync(join(tree, "lean", ".lake", "build", "bin", "verifier"), { force: true });
  const modules = ["node_modules", "tools/node_modules",
    ...readdirSync(join(repository, "pipeline")).map((d) => `pipeline/${d}/node_modules`)];
  for (const m of modules) {
    if (existsSync(join(repository, m)) && !existsSync(join(tree, m)))
      execFileSync("cp", ["-c", "-R", join(repository, m), join(tree, m)]);
  }
  const built = await exec("make", ["build"], { cwd: tree, log: logOf(r, t) });
  if (built.status !== 0) throw Error(`${t.id}: make build failed in ${tree}`);
}

const runNote = (r: Run): string => `
## This run

- You run under codex: your commands run in a sandbox without network. A
  command that opens the TypeScript compiler (\`run-cases.mts\`,
  \`verify-source.mts\`, \`make suite\`, \`make test\`, \`make census\`) and
  every git commit need escalated permissions: request them. Never push or
  fetch, and write nothing outside your worktree, \`${work(r)}\` and the
  stage store.
- Your worktree is set up: \`lean/.lake\`, the node_modules directories and
  \`make build\` are done.
- Write each commit record using only the terms of \`docs/GLOSSARY.md\`,
  plain words, and the names and terms of TypeScript and the code; explain
  any other term where it first appears, and use no words of process or
  status ("now", "approved", "reviewed"). Skip the brief's glossary check
  by a fresh agent.
- After you finish, the orchestrator runs \`make suite\` and \`make test\`,
  has the branch reviewed and merges it.
- Leave the worktree clean: everything committed. Your final message is
  your report.`;

function authorPrompt(r: Run, t: Task): string {
  const record = r.state.census;
  if (t.kind === "case")
    return readFileSync(join(repository, ".claude/skills/gap-round/brief.md"), "utf8")
      .replaceAll("<case>", t.id).replaceAll("<reason>", t.reason).replaceAll("<sites>", t.sites.join("; "))
      .replaceAll("<census record>", record).replaceAll("<scratch>", work(r)) + runNote(r);
  const given = join(work(r), "causes.json");
  if (t.kind === "repros" && existsSync(given))
    return `You prepare one gap iteration of TScert on the census record ${record} (its slices beside it) and its
refusals, ${join(work(r), "refusals.json")}. Read CLAUDE.md first; it is the authority. The round's causes are given,
in order, in ${given}; rank nothing. For each cause: find the census functions it blocks and their refusal sites in
the refusals and the slices; use the pipeline case it names, or the one that shows it, or add the smallest source
that reproduces that census refusal, its header naming the census functions it stands for, with its
pipeline/cases.mts entry as a gap, and check it reproduces the refusal (run-cases.mts <name>). A cause no census
function meets any more is left out, with the reason, in ${join(work(r), "ranking.md")}.

Write ${join(work(r), "ranking.md")} (each cause, its sites, its case) and ${join(work(r), "ranking.json")}, the
causes in the given order: {"cases": [{"case": "<name of pipeline/examples/<name>.ts>", "reason": "...",
"statements": n, "functions": n, "sites": ["file.mts#fn: what is refused", ...]}]}. Heavy runs take the lock
${heavy(r)} (until mkdir it 2>/dev/null; do sleep 20; done; <command>; rmdir it). Commit the cases you add as one
commit with a record in the format of .claude/skills/review/SKILL.md.
${runNote(r)}`;
  if (t.kind === "repros")
    return `You prepare one gap iteration of TScert: steps 2 and 3 of the gap-round skill below, on the census
record ${record} (its slices beside it) and its refusals, ${join(work(r), "refusals.json")}. Read CLAUDE.md first; it is the authority.

${section(".claude/skills/gap-round/SKILL.md", "## 2.")}

${section(".claude/skills/gap-round/SKILL.md", "## 3.")}

Write the confirmed ranking to ${join(work(r), "ranking.md")}, and the ${r.o.cases} open causes first by
blocked statements, each with the pipeline case that shows it (one you added if none did), to
${join(work(r), "ranking.json")}: {"cases": [{"case": "<name of pipeline/examples/<name>.ts>", "reason": "...",
"statements": n, "functions": n, "sites": ["file.mts#fn: what is refused", ...]}]}. Heavy runs take the lock
${heavy(r)} (until mkdir it 2>/dev/null; do sleep 20; done; <command>; rmdir it). Commit the cases you add as one
commit with a record in the format of .claude/skills/review/SKILL.md; add none when every cause has its case.
${runNote(r)}`;
  if (t.kind === "row")
    return `The verified census of main moved; record its movement in WORK.md's status table, in the row of
coverage of the front end, as CLAUDE.md's "Status" convention states. The census report is
${join(r.run, "census-report.txt")}, the records ${r.state.previous} (before) and ${r.state.verified} (after).
Commit with a record in the format of .claude/skills/review/SKILL.md; run node tests/docs.mts before.
${runNote(r)}`;
  return `Rebuild the gap-priorities deep dive (docs/deep-dives/gap-priorities/deck.mts) from the census
record ${record} and its refusals, ${join(work(r), "refusals.json")}, as the gap-round skill's step 6 states, step 2
of the skill done again on that record.

${section(".claude/skills/gap-round/SKILL.md", "## 2.")}

${section(".claude/skills/gap-round/SKILL.md", "## 6.")}

${section("docs/STYLE.md", "## Writing and checking a deck")}

Mark it since the version last approved (docs/STYLE.md, "A revised deck"). Build and check it with
make deck NAME=gap-priorities. Commit with a record in the format of .claude/skills/review/SKILL.md.
${runNote(r)}`;
}

/** The author's run, once, or again with `extra` appended. */
async function author(r: Run, t: Task, extra: string = ""): Promise<void> {
  const round = readdirSync(taskDir(r, t)).filter((n) => n.startsWith("report")).length;
  await codex(r, { model: t.kind === "case" ? r.o.agent : r.o.driver, cwd: treeOf(r, t), write: true, log: logOf(r, t),
    out: join(taskDir(r, t), round ? `report-${round}.md` : "report.md"), prompt: authorPrompt(r, t) + extra });
  t.authored = true;
  save(r);
}

const clean = (r: Run, t: Task): boolean => git(treeOf(r, t), "status", "--porcelain") === "";
const commits = (r: Run, t: Task): string[] =>
  git(treeOf(r, t), "rev-list", "--reverse", `main..${branchOf(t)}`).split("\n").filter(Boolean);
const patchId = (r: Run, t: Task): string =>
  execFileSync("sh", ["-c", `git diff main...${branchOf(t)} | git patch-id --stable`], { cwd: treeOf(r, t), encoding: "utf8" })
    .split(" ")[0] ?? "";

/** Main's tip under the branch: rebased onto it, or the author resolving
 * the conflict. */
async function integrate(r: Run, t: Task): Promise<boolean> {
  const tree = treeOf(r, t);
  if (gitOk(tree, "merge-base", "--is-ancestor", "main", "HEAD")) return true;
  if (gitOk(tree, "rebase", "-q", "main")) return true;
  gitOk(tree, "rebase", "--abort");
  await author(r, t, `\n\nMain moved. Rebase your branch onto main and resolve the conflicts; keep both sides of an
append conflict in WORK.md or docs/SOURCE-REWRITES.md. Run the cases you touch again.`);
  return clean(r, t) && gitOk(tree, "merge-base", "--is-ancestor", "main", "HEAD");
}

/** The task's gates on its branch's current tree, under the heavy lock;
 * true when they passed on this tree before. */
async function gate(r: Run, t: Task): Promise<{ passed: boolean; failure: string }> {
  const tree = treeOf(r, t), log = logOf(r, t), key = git(tree, "rev-parse", "HEAD^{tree}");
  if (t.gated === key) return { passed: true, failure: "" };
  const steps: [string, string[]][] = t.kind === "row" ? [["node", ["tests/docs.mts"]]]
    : t.kind === "deck" ? [["node", ["tests/docs.mts"]], ["node", ["dev/deck-cli.mts", "gap-priorities"]]]
    : [["make", ["build"]], ["make", ["suite"]], ["make", ["test"]]];
  return locked(heavy(r), async () => {
    for (const [command, args] of steps) {
      const ran = await exec(command, args, { cwd: tree, log });
      if (ran.status !== 0) return { passed: false, failure: `${command} ${args.join(" ")} failed:\n${ran.output.slice(-6000)}` };
    }
    t.gated = key;
    save(r);
    return { passed: true, failure: "" };
  });
}

const reviewSchema = { type: "object", additionalProperties: false, required: ["blocking", "findings"], properties: {
  blocking: { type: "boolean" }, findings: { type: "array", items: { type: "object", additionalProperties: false,
    required: ["blocking", "text"], properties: { blocking: { type: "boolean" }, text: { type: "string" } } } } } };

function decodeReview(text: string): { blocking: boolean; findings: { blocking: boolean; text: string }[] } {
  const v: unknown = JSON.parse(text);
  if (!(v && typeof v === "object" && "blocking" in v && typeof v.blocking === "boolean" && "findings" in v &&
    Array.isArray(v.findings)))
    throw Error("a review lacks a field");
  const findings = v.findings.map((f: unknown) => {
    if (!(f && typeof f === "object" && "blocking" in f && typeof f.blocking === "boolean" && "text" in f &&
      typeof f.text === "string"))
      throw Error("a review finding lacks a field");
    return { blocking: f.blocking, text: f.text };
  });
  return { blocking: v.blocking, findings };
}

function reviewPrompts(r: Run, t: Task): string[] {
  const goal = `Goal: TScert's gap work closes gap cases of its own front end, each verified or answered by a recorded
route of docs/SOURCE-REWRITES.md ("Deciding what a refusal of TScert's code calls for"), without weakening
soundness or gaining acceptance by trust added silently.`;
  if (t.kind === "deck")
    return [`${goal} Branch ${branchOf(t)} rebuilds the gap-priorities deep dive. Review it against the sources: run
git diff main...${branchOf(t)} here; check every number and claim of docs/deep-dives/gap-priorities/deck.mts against
the census record ${r.state.census}, its slices and the cases, and the deck against docs/STYLE.md. Blocking = a
claim the sources do not support, or a STYLE.md rule broken. Do not edit files.`];
  if (t.kind === "row")
    return [`${goal} Branch ${branchOf(t)} records the census movement in WORK.md. Run git diff main...${branchOf(t)}
here; check the row against ${join(r.run, "census-report.txt")} and CLAUDE.md's "Status" convention. Blocking = a
number the report does not give, or prose restating progress. Do not edit files.`];
  return [`${goal} Branch ${branchOf(t)} answers ${t.kind === "case" ? `case ${t.id} (reason: ${t.reason})` :
    "the iteration's ranking with new gap cases"}. Run git diff main...${branchOf(t)} and git log main..${branchOf(t)}
here, and review against CLAUDE.md. First: is the change an instance of an existing mechanism
(docs/DESIGN.md, "General mechanisms"), which, or what does it duplicate? Then: is it general and principled, or
does it restrict TScert to fit the mechanism; does it erase a contract, widen trust silently or weaken a soundness
boundary CLAUDE.md states; does each new rule have its Lean checker and theorem, a positive and a negative pipeline
case and forged-claim controls; is the trust of each model of external code stated; does each new case reproduce
the census refusal it stands for. Blocking = a soundness, trust or principle problem, or a missing required test or
record. Do not edit files.`];
}

/** Reviews until no blocking finding, the reviewer implementing them;
 * true when the branch's patch is approved. */
async function review(r: Run, t: Task): Promise<boolean> {
  for (let round = 0; ; round++) {
    const patch = patchId(r, t);
    if (t.reviewed === patch) return true;
    const blocking: string[] = [];
    for (const [i, prompt] of reviewPrompts(r, t).entries()) {
      const text = await codex(r, { model: r.o.reviewer, cwd: treeOf(r, t), write: false, log: logOf(r, t), prompt,
        schema: reviewSchema, out: join(taskDir(r, t), `review-${round}-${i}.json`) });
      blocking.push(...decodeReview(text).findings.filter((f) => f.blocking).map((f) => f.text));
    }
    if (!blocking.length) { t.reviewed = patch; save(r); return true; }
    if (round === 2) return false;
    await codex(r, { model: r.o.reviewer, cwd: treeOf(r, t), write: true, log: logOf(r, t),
      out: join(taskDir(r, t), `fix-${round}.md`), prompt: `Implement these blocking review findings on branch
${branchOf(t)} in this worktree, and commit with records in the format of .claude/skills/review/SKILL.md. Run the
cases you touch.\n\n${blocking.map((b, i) => `${i + 1}. ${b}`).join("\n\n")}\n${runNote(r)}` });
    if (!clean(r, t) || !(await integrate(r, t)) || !(await gate(r, t)).passed) return false;
  }
}


/** Fails unless the main checkout is on main and clean. */
function mainReady(): void {
  if (git(repository, "rev-parse", "--abbrev-ref", "HEAD") !== "main") throw Error(`${repository} is not on main`);
  if (git(repository, "status", "--porcelain", "--untracked-files=no") !== "") throw Error(`${repository} has changes`);
}

/** A task from its author's run to its merge into main. */
async function runTask(r: Run, t: Task): Promise<void> {
  if (t.status !== "pending") return;
  await setUp(r, t);
  if (!t.authored) await author(r, t);
  if (!clean(r, t)) return close(r, t, "incomplete", "the author left uncommitted changes");
  if (!commits(r, t).length) return close(r, t, "incomplete", "no commit");
  if (!(await integrate(r, t))) return close(r, t, "incomplete", "main's tip not integrated");
  let gated = await gate(r, t);
  if (!gated.passed) {
    await author(r, t, `\n\nThe orchestrator's gates failed on your branch; fix it and commit.\n\n${gated.failure}`);
    if (!clean(r, t) || !(await integrate(r, t))) return close(r, t, "incomplete", "gates failed, then not integrated");
    gated = await gate(r, t);
    if (!gated.passed) return close(r, t, "incomplete", `gates failed twice (${logOf(r, t)})`);
  }
  if (!(await review(r, t))) return close(r, t, "incomplete", "blocking review findings after two fix rounds");
  await serially(async () => {
    mainReady();
    if (!(await integrate(r, t))) return close(r, t, "incomplete", "main's tip not integrated");
    if (!(await gate(r, t)).passed) return close(r, t, "incomplete", "gates failed on main's tip");
    if (!(await review(r, t))) return close(r, t, "incomplete", "blocking review findings on main's tip");
    git(repository, "merge", "-q", "--ff-only", branchOf(t));
    const built = await locked(heavy(r), () => exec("make", ["build"], { cwd: repository, log: logOf(r, t) }));
    if (built.status !== 0) throw Error(`make build failed on main after merging ${t.id}`);
    close(r, t, "merged", git(repository, "rev-parse", "--short", "HEAD"));
  });
}

// ---------------------------------------------------------------- phases

const newTask = (id: string, kind: Kind, o: Partial<Task> = {}): Task => ({ id, kind, status: "pending", note: "",
  reason: "", sites: [], statements: 0, functions: 0, authored: false, gated: "", reviewed: "", ...o });

/** A census on main under the heavy lock; its record's path. */
async function census(r: Run): Promise<string> {
  const free = statfsSync(tmpdir());
  if (free.bavail * free.bsize < 30 * 2 ** 30) throw Error(`less than 30 GiB free in ${tmpdir()}`);
  const log = join(r.run, "census.log");
  const ran = await locked(heavy(r), () => exec("make", ["census"], { cwd: repository, log }));
  const record = /^record: (.+)$/m.exec(ran.output)?.[1];
  if (ran.status !== 0 || !record) throw Error(`the census failed (${log})`);
  return record;
}

/** A census record's refusals, written to `work/refusals.json`. */
function writeRefusals(r: Run): void {
  writeFileSync(join(work(r), "refusals.json"), execFileSync(process.execPath, ["dev/census.mts", "refusals", r.state.census],
    { cwd: repository, encoding: "utf8", maxBuffer: 64 * 2 ** 20 }));
}

/** The commit a census record was taken at. */
function recordCommit(record: string): { commit: string; status: string } {
  const v: unknown = JSON.parse(readFileSync(record, "utf8"));
  if (!(v && typeof v === "object" && "source" in v && v.source && typeof v.source === "object" && "commit" in v.source &&
    typeof v.source.commit === "string"))
    throw Error(`${record} has no source commit`);
  return { commit: v.source.commit, status: "status" in v && typeof v.status === "string" ? v.status : "" };
}

/** Whether `commit` has main's code: the directories every stage and the census read, this command aside. */
const mainsCode = (commit: string): boolean =>
  gitOk(repository, "diff", "--quiet", commit, "main", "--", "tools", "pipeline", "lean", "ocaml-producer", "dev", ":(exclude)dev/gap-iteration.mts");

async function rank(r: Run): Promise<void> {
  if (!r.state.census) {
    const given = r.o.census;
    r.state.census = given && recordCommit(given).status !== "diagnostic" && mainsCode(recordCommit(given).commit)
      ? given : await census(r);
    if (given && r.state.census !== given) process.stderr.write(`${given} is not a census of main's code\n`);
    r.state.previous ||= r.state.census;
    save(r);
    writeRefusals(r);
  }
  if (!r.state.tasks.some((t) => t.kind === "repros")) { r.state.tasks.push(newTask("repros", "repros")); save(r); }
  const repros = r.state.tasks.find((t) => t.kind === "repros");
  if (repros?.status === "pending") {
    await setUp(r, repros);
    if (!repros.authored) await author(r, repros);
    if (commits(r, repros).length) await runTask(r, repros);
    else close(r, repros, "merged", "every cause has its case");
  }
  if (repros?.status !== "merged") throw Error(`the ranking's cases are not merged: ${repros?.note}`);
  if (r.state.tasks.some((t) => t.kind === "case")) return;
  const v: unknown = JSON.parse(readFileSync(join(work(r), "ranking.json"), "utf8"));
  if (!(v && typeof v === "object" && "cases" in v && Array.isArray(v.cases))) throw Error("ranking.json has no cases");
  for (const c of v.cases.slice(0, r.o.cases)) {
    if (!(c && typeof c === "object" && "case" in c && typeof c.case === "string" && /^[a-z0-9-]+$/.test(c.case) &&
      "reason" in c && typeof c.reason === "string" && "statements" in c && typeof c.statements === "number" &&
      "functions" in c && typeof c.functions === "number" && "sites" in c && isStrings(c.sites)))
      throw Error("a case of ranking.json lacks a field");
    if (!existsSync(join(repository, "pipeline", "examples", `${c.case}.ts`))) throw Error(`no case ${c.case} on main`);
    r.state.tasks.push(newTask(c.case, "case", { reason: c.reason, statements: c.statements, functions: c.functions,
      sites: c.sites }));
  }
  save(r);
}

async function workPhase(r: Run): Promise<void> {
  const cases = r.state.tasks.filter((t) => t.kind === "case" && t.status === "pending");
  let next = 0, paused: Paused | null = null;
  const lane = async (): Promise<void> => {
    while (!paused && next < cases.length) {
      const t = cases[next++];
      if (!t) return;
      try { await runTask(r, t); } catch (e) {
        if (e instanceof Paused) paused = e;
        else close(r, t, "incomplete", e instanceof Error ? e.message : String(e));
      }
    }
  };
  await Promise.all(Array.from({ length: Math.min(r.o.parallel, cases.length) }, lane));
  if (paused) throw paused;
}

async function finish(r: Run): Promise<void> {
  if (r.state.tasks.some((t) => t.kind === "case" && t.status === "pending")) throw Error("cases are pending; run work first");
  if (!r.state.previous) throw Error("no previous census: pass --previous <record>");
  mainReady();
  if (!r.state.verified) {
    for (const target of ["suite", "test"]) {
      const ran = await locked(heavy(r), () => exec("make", [target], { cwd: repository, log: join(r.run, "main.log") }));
      if (ran.status !== 0) throw Error(`make ${target} fails on main (${join(r.run, "main.log")})`);
    }
    r.state.verified = await census(r);
    save(r);
    const report = execFileSync(process.execPath, ["dev/census.mts", "report", r.state.previous, r.state.verified],
      { cwd: repository, encoding: "utf8", maxBuffer: 64 * 2 ** 20 });
    writeFileSync(join(r.run, "census-report.txt"), report);
  }
  if (!r.state.tasks.some((t) => t.kind === "row")) { r.state.tasks.push(newTask("census-row", "row")); save(r); }
  for (const t of r.state.tasks.filter((t) => t.kind === "row")) await runTask(r, t);
  if (!r.state.tasks.some((t) => t.kind === "deck")) {
    r.state.census = r.state.verified;
    writeRefusals(r);
    r.state.tasks.push(newTask("deck", "deck"));
    save(r);
  }
  for (const t of r.state.tasks.filter((t) => t.kind === "deck")) await runTask(r, t);
  const lines = r.state.tasks.map((t) => {
    const reports = existsSync(taskDir(r, t)) ? readdirSync(taskDir(r, t)).filter((n) => n.startsWith("report")).sort() : [];
    const last = reports.at(-1);
    return `### ${t.id} (${t.kind}): ${t.status}${t.note ? `, ${t.note}` : ""}\n\n${
      last ? readFileSync(join(taskDir(r, t), last), "utf8") : ""}`;
  }).join("\n\n");
  writeFileSync(join(r.run, "inputs.md"), `${readFileSync(join(r.run, "census-report.txt"), "utf8")}\n\n${lines}\n`);
  await codex(r, { model: r.o.driver, cwd: r.run, write: false, log: join(r.run, "report.log"), out: join(r.run, "report.md"),
    prompt: `Write the report of this gap iteration from inputs.md in this directory, in the form below. Every
number comes from inputs.md. End with: nothing is pushed.\n\n${section(".claude/skills/gap-round/SKILL.md", "## The report")}` });
}

// ---------------------------------------------------------------- main

const [phase, ...rest] = process.argv.slice(2);
const phases = ["rank", "work", "finish", "all"];
if (!phase || !phases.includes(phase)) throw Error(`usage: gap-iteration.mts ${phases.join("|")} [options]; see the header`);
const o = options(rest);
const run = resolve(o.run ?? join(lockRoot, new Date().toISOString().replace(/[:.]/g, "-")));
mkdirSync(join(run, "work"), { recursive: true });
mkdirSync(join(run, "tasks"), { recursive: true });
if (o.causes && !existsSync(join(run, "work", "causes.json"))) writeFileSync(join(run, "work", "causes.json"), readFileSync(o.causes));
if (!existsSync(join(run, "state.json"))) {
  if (phase !== "rank" && phase !== "all") throw Error(`${run} has no state.json: start with rank or all`);
  mainReady();
  writeState(run, { repository, base: git(repository, "rev-parse", "main"), census: "", previous: o.previous ?? "",
    verified: "", tasks: [] });
}
const state = readState(run);
// A rerun retries every incomplete task from where it stopped.
for (const t of state.tasks) if (t.status === "incomplete") Object.assign(t, { status: "pending", note: "" });
if (o.previous && !state.previous) state.previous = o.previous;
const controller = join(lockRoot, "controller.lock");
mkdirSync(lockRoot, { recursive: true });
try { mkdirSync(controller); } catch { throw Error(`another gap iteration runs (${controller})`); }
const release = (): void => rmSync(controller, { recursive: true, force: true });
process.on("SIGINT", () => { release(); process.exit(130); });
process.stderr.write(`run: ${run}\n`);
const r: Run = { run, o, state };
try {
  if (phase === "rank" || phase === "all") await rank(r);
  if (phase === "work" || phase === "all") await workPhase(r);
  if (phase === "finish" || phase === "all") await finish(r);
  process.stdout.write(`${phase} done: ${run}${existsSync(join(run, "report.md")) ? `\nreport: ${join(run, "report.md")}` : ""}\n`);
} catch (e) {
  save(r);
  if (e instanceof Paused) { process.stderr.write(`paused: ${e.message}; repeat the command to resume\n`); process.exitCode = 3; }
  else throw e;
} finally {
  release();
}
