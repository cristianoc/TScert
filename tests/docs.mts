// Checks the Markdown documents in this repository: that every relative link
// and anchor resolves, that a link naming a section number names the section
// its anchor points at, that math renders with KaTeX and avoids the forms
// GitHub cannot render, and that cited authors are named only inside links to
// REFERENCES.md.
//   node tests/docs.mts
import { readdirSync, readFileSync, existsSync, realpathSync } from "node:fs";
import { createRequire } from "node:module";
import { dirname, join, relative, resolve } from "node:path";

const root = resolve(import.meta.dirname, "..");
/** KaTeX's renderer, the one member this check calls: the module is plain
 * JavaScript, so it is tested to have it. */
interface Katex {
  renderToString(tex: string, options: { displayMode: boolean; throwOnError: boolean; strict: string }): string;
}
const isKatex = (module: unknown): module is Katex =>
  !!module && typeof module === "object" && "renderToString" in module && typeof module.renderToString === "function";
const loaded: unknown = createRequire(join(root, "tools", "package.json"))("katex");
if (!isKatex(loaded)) throw Error("katex has no renderToString");
const katex = loaded;

/** Directories holding no maintained documents: dependencies and build output.
 * A directory with a `.git` entry of its own is another checkout, such as an
 * agent's worktree under `.claude/worktrees/`, and holds that checkout's documents. */
const excluded = new Set(["node_modules", ".lake", "_build"]);

/** A symbolic link to a document is that document under another name: it is
 * checked only as a link, whose target must be a document checked here. */
const links: string[] = [];
function markdownFiles(dir: string): string[] {
  const found: string[] = [];
  for (const entry of readdirSync(dir, { withFileTypes: true })) {
    if (excluded.has(entry.name)) continue;
    const path = join(dir, entry.name);
    if (entry.isSymbolicLink()) { if (entry.name.endsWith(".md")) links.push(path); }
    else if (entry.isDirectory()) {
      if (!existsSync(join(path, ".git"))) for (const file of markdownFiles(path)) found.push(file);
    }
    else if (entry.name.endsWith(".md")) found.push(path);
  }
  return found;
}

/** The document with code fences removed, math fences kept. */
function withoutCode(text: string): string {
  const out: string[] = [];
  let fence: string | undefined;
  for (const line of text.split("\n")) {
    const opening = /^\s*(```+)(.*)$/.exec(line);
    if (fence === undefined) {
      if (opening) fence = (opening[2] ?? "").trim();
      if (!opening || fence === "math") out.push(line);
    } else if (opening && (opening[2] ?? "").trim() === "") {
      if (fence === "math") out.push(line);
      fence = undefined;
    } else if (fence === "math") out.push(line);
  }
  return out.join("\n");
}

const inlineMath = /\$`([^`]*)`\$/g;
/** Prose: no math, and no inline code. */
function prose(text: string): string {
  return text.replace(/```math\n[\s\S]*?```/g, "").replace(inlineMath, " ").replace(/`[^`\n]*`/g, " ");
}

/** GitHub's heading slug. */
function slug(heading: string): string {
  return heading.trim().toLowerCase().replace(/<[^>]+>/g, "").replace(inlineMath, "$1").replace(/[`*_]/g, "")
    .replace(/\[([^\]]*)\]\([^)]*\)/g, "$1").replace(/[^\p{L}\p{N}\s-]/gu, "").replace(/\s/g, "-");
}

const anchors = new Map<string, Map<string, string>>();
function anchorsOf(file: string): Map<string, string> {
  const known = anchors.get(file);
  if (known) return known;
  const found = new Map<string, string>();
  const seen = new Map<string, number>();
  const text = withoutCode(readFileSync(file, "utf8"));
  for (const m of text.matchAll(/^#{1,6}\s+(.*)$/gm)) {
    const heading = m[1] ?? "";
    const s = slug(heading);
    const n = seen.get(s) ?? 0;
    seen.set(s, n + 1);
    found.set(n ? `${s}-${n}` : s, heading);
  }
  for (const m of text.matchAll(/<a\s+id="([^"]+)"/g)) found.set(m[1] ?? "", "");
  anchors.set(file, found);
  return found;
}

const sectionNumber = (s: string): number[] => s.split(".").map(Number);
function compare(a: number[], b: number[]): number {
  for (let i = 0; i < Math.max(a.length, b.length); i++) {
    const d = (a[i] ?? 0) - (b[i] ?? 0);
    if (d) return d;
  }
  return 0;
}
/** Whether heading number `h` lies in `§n` or `§n–m`, a prefix counting as its section. */
function numbered(text: string, heading: string): boolean {
  const cited = /§\s*([0-9]+(?:\.[0-9]+)*)(?:\s*[–-]\s*([0-9]+(?:\.[0-9]+)*))?/.exec(text);
  const own = /^([0-9]+(?:\.[0-9]+)*)\.?\s/.exec(heading);
  if (!cited || !own) return true;
  const h = sectionNumber(own[1] ?? "");
  const from = sectionNumber(cited[1] ?? "");
  const upper = cited[2];
  const to = upper ? sectionNumber(upper) : from;
  const within = (n: number[]) => h.length >= n.length ? compare(h.slice(0, n.length), n) : compare(h, n.slice(0, h.length));
  return within(from) >= 0 && within(to) <= 0;
}

/** Forms GitHub's math renderer refuses or garbles (see the global agent notes). */
const unrenderable: [RegExp, string][] = [
  [/\$\$/g, "`$$` display math: use a ```math fence"],
  [/\\operatorname/g, "`\\operatorname`: use `\\mathrm`"],
  [/\\llbracket|\\rrbracket/g, "`\\llbracket`: use ⟦ ⟧"],
  [/(?<!\\)\\\(|(?<!\\)\\\[/g, "`\\(` or `\\[`: use $`…`$ or a ```math fence"],
];

const files = markdownFiles(root);
const problems: string[] = [];
for (const link of links) {
  const target = existsSync(link) ? realpathSync(link) : undefined;
  if (!target || !files.includes(target))
    problems.push(`${relative(root, link)}: symbolic link to a document this check does not cover`);
}
const fail = (file: string, message: string): number => problems.push(`${relative(root, file)}: ${message}`);

for (const file of files) {
  const raw = readFileSync(file, "utf8");
  const text = withoutCode(raw);

  for (const m of prose(text).matchAll(/\[([^\]]*)\]\(([^)\s]+)\)/g)) {
    const [, label = "", url = ""] = m;
    if (/^[a-z]+:/i.test(url)) continue;
    const [path = "", anchor] = url.split("#");
    const target = path ? resolve(dirname(file), decodeURI(path)) : file;
    if (path && !existsSync(target)) { fail(file, `link to missing file ${url}`); continue; }
    if (anchor === undefined || !target.endsWith(".md")) continue;
    const heading = anchorsOf(target).get(decodeURIComponent(anchor));
    if (heading === undefined) fail(file, `link to missing anchor ${url}`);
    else if (!numbered(label, heading)) fail(file, `[${label}] points at "${heading}"`);
  }

  const maths = [...text.matchAll(/```math\n([\s\S]*?)```/g)].map((m): [string, boolean] => [m[1] ?? "", true])
    .concat([...text.matchAll(inlineMath)].map((m): [string, boolean] => [m[1] ?? "", false]));
  for (const [tex, displayMode] of maths) {
    try { katex.renderToString(tex, { displayMode, throwOnError: true, strict: "ignore" }); }
    catch (error) { fail(file, `KaTeX: ${String(error instanceof Error ? error.message : error).split("\n")[0]} in ${tex.replace(/\s+/g, " ").slice(0, 60)}`); }
  }
  const words = prose(text);
  for (const [pattern, remedy] of unrenderable) {
    const count = words.match(pattern)?.length ?? 0;
    if (count) fail(file, `${count}× ${remedy}`);
  }
}

// Citations: an author of a paper in REFERENCES.md (an entry whose heading
// carries a year) is named only inside a link to that document.
const references = join(root, "docs", "REFERENCES.md");
const authors = new Set([...readFileSync(references, "utf8").matchAll(/^### (.+?) (?:19|20)\d\d\b/gm)]
  .flatMap((m) => (m[1] ?? "").replace(/\bet al\.?/g, "").split(/,| and /))
  .flatMap((part) => [...part.matchAll(/\p{Lu}[\p{L}'’-]+/gu)].map((w) => w[0]).slice(-1)));
for (const file of files) {
  if (file === references) continue;
  const text = prose(withoutCode(readFileSync(file, "utf8")));
  const links = [...text.matchAll(/\[[^\]]*\]\(([^)\s]*)\)/g)]
    .filter((m) => resolve(dirname(file), (m[1] ?? "").split("#")[0] ?? "") === references)
    .map((m) => [m.index ?? 0, (m.index ?? 0) + m[0].length]);
  for (const author of authors)
    for (const m of text.matchAll(new RegExp(`(?<![\\p{L}])${author}(?![\\p{L}])`, "gu")))
      if (!links.some(([a = 0, b = 0]) => a <= (m.index ?? 0) && (m.index ?? 0) < b))
        fail(file, `names ${author} outside a link to REFERENCES.md`);
}

for (const p of problems) process.stdout.write(`${p}\n`);
process.stdout.write(`docs: ${files.length} documents, ${problems.length} problems\n`);
process.exitCode = problems.length ? 1 : 0;
