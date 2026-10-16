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
import { parseRecord, pageBody, CSS, type CommitRecord, type Group } from "./record-render.mts";

const git = (args: string[], input?: string): string =>
  execFileSync("git", args, { input, encoding: "utf8", maxBuffer: 64 << 20, stdio: ["pipe", "pipe", "ignore"] });

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
