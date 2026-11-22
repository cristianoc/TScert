// Translate v0.94 effect annotations in a clean, detached census worktree.
// Record the translated tree as a reproducible child of the release commit.
import { execFileSync } from "node:child_process";
import { readdirSync, readFileSync, writeFileSync } from "node:fs";
import { join, resolve } from "node:path";
import { close, openText } from "../tools/fragment-parse.mts";
import { syntax as ts } from "../tools/syntax.mts";

type Node = Parameters<typeof ts.isIdentifier>[0];

const release = "ae20a6c6b62705b42d9e049c6fc90f0bad10b8ed";
const corpus = "a4efe327c2d3ed4ac7077874841a74b83381127d";
if (process.argv.length !== 3 || !process.argv[2]) throw Error("usage: prepare-v094-census.mts <release worktree>");
const cwd = resolve(process.argv[2]);
const git = (args: string[]): string => execFileSync("git", args, { cwd, encoding: "utf8" }).trim();
if (git(["rev-parse", "HEAD"]) !== release || git(["status", "--porcelain"]) ||
    git(["rev-parse", "--abbrev-ref", "HEAD"]) !== "HEAD")
  throw Error("census preparation requires a clean detached v0.94 worktree");

let count = 0;
try {
  const tools = join(cwd, "tools");
  for (const name of readdirSync(tools).sort()) {
    if (!name.endsWith(".mts")) continue;
    const path = join(tools, name);
    const source = readFileSync(path, "utf8");
    if (!source.includes("Within")) continue;
    const file = openText(path, source);
    const edits: { start: number; end: number; text: string }[] = [];
    const edit = (node: Node, text: string): void => {
      edits.push({ start: node.getStart(file), end: node.end, text });
    };
    const visit = (node: Node): void => {
      if (ts.isTypeReferenceNode(node) && ts.isIdentifier(node.typeName) && node.typeName.text === "Within") {
        const footprint = node.typeArguments?.[0];
        if (node.typeArguments?.length !== 2 || !footprint || !ts.isTypeLiteralNode(footprint))
          throw Error(`${name}: unexpected Within annotation at ${node.pos}`);
        edit(node.typeName, "Modifies");
        const seen = new Set<string>();
        for (const member of footprint.members) {
          if (!ts.isPropertySignatureDeclaration(member) || !ts.isIdentifier(member.name) ||
              seen.has(member.name.text))
            throw Error(`${name}: unexpected Within field at ${member.pos}`);
          const key = member.name.text;
          seen.add(key);
          if (key === "value") edit(member.name, "values");
          else if (key === "store") edit(member.name, "spines");
          else if (key !== "onThrow") throw Error(`${name}: unexpected Within field ${key}`);
        }
        if (!seen.has("value") || !seen.has("store"))
          throw Error(`${name}: incomplete Within annotation at ${node.pos}`);
        count++;
      }
      node.forEachChild(visit);
    };
    visit(file);
    if (edits.length === 0) continue;
    let translated = source;
    for (const { start, end, text } of edits.sort((a, b) => b.start - a.start))
      translated = translated.slice(0, start) + text + translated.slice(end);
    writeFileSync(path, translated);
  }
  const declaration = join(tools, "resolvable.d.ts");
  const header = readFileSync(declaration, "utf8");
  const old = header.indexOf("// A signature's result `Within<F, T>`");
  if (old < 0 || !header.endsWith("type Within<F extends Footprint, T> = T;\n"))
    throw Error("unexpected v0.94 effect declarations");
  writeFileSync(declaration, header.slice(0, old) + "type Modifies<P, T> = T;\n");
} finally {
  close();
}

git(["add", "--update", "--", "tools"]);
const tree = git(["write-tree"]);
const env = { ...process.env,
  GIT_AUTHOR_NAME: "TScert census", GIT_AUTHOR_EMAIL: "census@tscert.invalid",
  GIT_COMMITTER_NAME: "TScert census", GIT_COMMITTER_EMAIL: "census@tscert.invalid",
  GIT_AUTHOR_DATE: "2026-11-04T00:00:00Z", GIT_COMMITTER_DATE: "2026-11-04T00:00:00Z" };
const commit = execFileSync("git", ["-c", "commit.gpgSign=false", "commit-tree", tree, "-p", release,
  "-m", "Translate v0.94 census effect annotations"], { cwd, env, encoding: "utf8" }).trim();
if (commit !== corpus) throw Error(`v0.94 census preparation produced ${commit}, expected ${corpus}`);
git(["reset", "--soft", commit]);
console.log(`Translated ${count} annotations for the v0.94 corpus at ${commit}`);
