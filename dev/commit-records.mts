/* Renders commit records as a review page: one card per commit, and for
 * branch ranges a summary of what each branch changes and where branches
 * overlap. A record is a commit message (or a note on refs/notes/records,
 * which takes precedence) in the format the `review` skill states: a subject,
 * prose sections ("Example:", "Rule:", indented blocks) and git trailers.
 *
 *   node tools/commit-records.mts --out review.html bb180be19
 *   node tools/commit-records.mts --out review.html cf3fbb3c1..branch-a cf3fbb3c1..branch-b
 *   --fragment omits the document skeleton (for an Artifact publish).
 */
import { execFileSync } from "node:child_process";
import { writeFileSync } from "node:fs";
import { parseRecord, pageBody, CSS, type CommitRecord, type Example, type Group } from "./record-render.mts";

const git = (args: string[], input?: string): string =>
  execFileSync("git", args, { input, encoding: "utf8", maxBuffer: 64 << 20, stdio: ["pipe", "pipe", "ignore"] });

/** A file's text at a revision, or undefined where it has none. */
function at(rev: string, path: string): string | undefined {
  try { return git(["show", `${rev}:${path}`]); } catch { return undefined; }
}

/** The pipeline cases an Effect section names, as the commit has them (a
 * removed case as its parent had it): the program, its kind, and the span its
 * expected diagnostic names, from `pipeline/cases.mts`. */
function examplesOf(rev: string, text: string): Map<string, Example> {
  const found = new Map<string, Example>();
  const effect = /^Effect:\s*\n((?: {2,}.*\n?|\s*\n)*)/m.exec(text);
  if (!effect) return found;
  const names = effect[1].split("\n").map(l => l.trim().split(/\s{3,}/)[0]).filter(n => n && /^[\w/.-]+$/.test(n));
  for (const name of names) {
    for (const r of [rev, `${rev}^`]) {
      const source = at(r, `pipeline/examples/${name}.ts`);
      if (source === undefined) continue;
      const cases = at(r, "pipeline/cases.mts") ?? "";
      const i = cases.indexOf(`("${name}"`);
      const next = i < 0 ? -1 : cases.slice(i + 1).search(/\n {2}(?:\{ \.\.\.)?(?:positive|negative|gap)\(/);
      const entry = i < 0 ? "" : cases.slice(i, next < 0 ? undefined : i + 1 + next);
      const kind = /(positive|negative|gap)$/.exec(cases.slice(Math.max(0, i - 10), i))?.[1];
      const span = /\\\[(\d+),(\d+)\\\)/.exec(entry);
      found.set(name, { source, kind, span: span ? [Number(span[1]), Number(span[2])] : undefined });
      break;
    }
  }
  return found;
}

/** The record of one commit: its note if it has one, else its message. */
function readRecord(rev: string): CommitRecord {
  let text = "";
  try { text = git(["notes", "--ref=records", "show", rev]); } catch { /* no note */ }
  const message = git(["show", "-s", "--format=%B", rev]);
  if (!text.trim()) text = message;
  return parseRecord(text, {
    sha: git(["rev-parse", "--short=9", rev]).trim(),
    author: git(["show", "-s", "--format=%an · %ad", "--date=format:%b %d, %H:%M", rev]).trim(),
    stat: git(["show", "--stat", "--format=", rev]).trimEnd().split("\n").filter(Boolean),
    message,
    examples: examplesOf(rev, text),
  });
}

function group(arg: string): Group {
  if (!arg.includes("..")) return { name: arg, records: [readRecord(arg)], files: [] };
  const [base, tip] = arg.split("..");
  const revs = git(["rev-list", "--reverse", "--no-merges", arg]).split("\n").filter(Boolean);
  return {
    name: tip, range: arg, records: revs.map(readRecord),
    files: git(["diff", "--name-only", `${base}...${tip}`]).split("\n").filter(Boolean),
  };
}

const args = process.argv.slice(2);
const outAt = args.indexOf("--out");
if (outAt < 0 || outAt + 1 >= args.length) throw new Error("usage: commit-records.mts --out <file.html> [--fragment] <rev | base..branch>...");
const outFile = args[outAt + 1];
const fragment = args.includes("--fragment");
const targets = args.filter((a, i) => i !== outAt && i !== outAt + 1 && a !== "--fragment");
const groups = targets.map(group);
const head = `<title>Commit Records</title>
<link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=IBM+Plex+Sans:wght@400;500;600&family=IBM+Plex+Serif:ital,wght@0,500;0,600;1,400&family=IBM+Plex+Mono:wght@400;500&family=STIX+Two+Text:ital,wght@0,400;0,500;1,400&display=swap">
<style>${CSS}</style>`;
const body = pageBody(groups);
writeFileSync(outFile, fragment ? `${head}\n${body}\n`
  : `<!doctype html>\n<html><head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">\n${head}</head><body>${body}</body></html>\n`);
console.log(outFile);
