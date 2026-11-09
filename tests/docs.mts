// Checks the Markdown documents in this repository: that every relative link
// and anchor resolves, that a link naming a section number names the section
// its anchor points at, that math renders with KaTeX and avoids the forms
// GitHub cannot render, that cited authors are named only inside links to
// REFERENCES.md, and that a code comment's `(<document>.md, "Section")` or
// `<DOCUMENT> §n` citation names a section the document holds, and that
// ANNOTATIONS.md has an entry for exactly the annotations TScert reads.
//   node tests/docs.mts
import { readdirSync, readFileSync, realpathSync } from "node:fs";
import { present } from "../tools/files.mts";
import { annotationTags } from "../tools/bound-annotations.mts";
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
      if (!present(join(path, ".git"))) for (const file of markdownFiles(path)) found.push(file);
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
  const target = present(link) ? realpathSync(link) : undefined;
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
    if (path && !present(target)) { fail(file, `link to missing file ${url}`); continue; }
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
  // Single-dollar math, which GitHub reads after Markdown has taken its
  // escapes: a `$`-delimited span holding a TeX command, a sub- or superscript.
  const dollars = words.match(/(?<![\\$\w])\$(?=\S)[^$\n]*?(?:\\[A-Za-z]+|[_^]\{)[^$\n]*?(?<=\S)\$(?![\w$])/g)?.length ?? 0;
  if (dollars) fail(file, `${dollars}× \`$…$\` inline math: use $\`…\`$`);
  // LaTeX in a plain code span, which renders as code.
  const spans = [...text.replace(/```math\n[\s\S]*?```/g, "").replace(inlineMath, " ").matchAll(/`([^`\n]*)`/g)]
    .filter((m) => /\\(?:math[a-z]+|text|frac|operatorname|forall|exists|vdash|models|sqsubseteq|subseteq|langle|rangle|mapsto|Gamma|Delta|lambda|sigma|tau|rho)(?![A-Za-z])/.test(m[1] ?? "")).length;
  if (spans) fail(file, `${spans}× LaTeX in a code span: use $\`…\`$`);
  // Inline math inside emphasis, which breaks the math.
  const emphasized = text.replace(/```math\n[\s\S]*?```/g, "")
    .match(/(?<![*\w])\*(?!\s)[^*\n]*\$`[^`\n]*`\$[^*\n]*?(?<!\s)\*(?![*\w])/g)?.length ?? 0;
  if (emphasized) fail(file, `${emphasized}× inline math inside emphasis: put the math outside the emphasis`);
  // A math fence inside a list item whose text holds inline math renders as
  // code: the item's later indented lines are its own.
  let item: { math: boolean } | undefined, fenced = 0;
  for (const line of text.split("\n")) {
    if (/^\s*(?:[-*+]|\d+\.)\s/.test(line) && !/^\s{2,}/.test(line)) item = { math: inlineMath.test(line) };
    else if (item && /^\s+\S/.test(line)) {
      if (/^\s+```math/.test(line) && item.math) fenced++;
      else if (inlineMath.test(line)) item.math = true;
    } else if (/\S/.test(line)) item = undefined;
    inlineMath.lastIndex = 0;
  }
  if (fenced) fail(file, `${fenced}× a math fence in a list item after inline math: put the display outside the list`);
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

// Citations in code: a comment or string citing sections as
// `(<document>.md, "Title", "Title"…)` names a document of docs/ or of the
// root and sections it holds, each a heading or a paragraph opening with a
// bold label, compared without case, backticks, a section number or a closing
// period; a citation `<DOCUMENT>[.md] §n, §m…` of such a document names
// numbered headings it holds, both ends of a range `§n–m` included. A
// citation may wrap across comment lines. A title cited without quotes, a
// bare `§n` naming no document, whether an existing anchor or section is the
// one a citation means, and the Lean and code names a document's code spans
// hold are not checked here.
const codeRoots = ["tools", "pipeline", "dev", "tests", "lean/Verification", "ocaml-producer"];
const codeFile = /\.(mts|ts|lean|ml|mli|sh|c)$/;
function codeFiles(dir: string): string[] {
  const found: string[] = [];
  for (const entry of readdirSync(dir, { withFileTypes: true })) {
    if (excluded.has(entry.name) || entry.isSymbolicLink()) continue;
    const path = join(dir, entry.name);
    if (entry.isDirectory()) found.push(...codeFiles(path));
    else if (codeFile.test(entry.name)) found.push(path);
  }
  return found;
}
const sectionKey = (title: string): string =>
  title.replace(/[`*]/g, "").replace(/^§?[0-9]+(?:\.[0-9]+)*\.?\s+/, "").replace(/\.$/, "").replace(/\s+/g, " ").trim().toLowerCase();
/** A document of docs/ or of the root: its section keys and its headings' numbers. */
interface Sections { keys: Set<string>; numbers: Set<string> }
const sections = new Map<string, Sections | undefined>();
function sectionsOf(document: string): Sections | undefined {
  if (sections.has(document)) return sections.get(document);
  const path = [join(root, "docs", document), join(root, document)].find((p) => present(p));
  const text = path === undefined ? undefined : withoutCode(readFileSync(path, "utf8"));
  const found = text === undefined ? undefined : {
    keys: new Set([...text.matchAll(/^(?:#{1,6}\s+(.*)|\*\*(.+?)\*\*)/gm)].map((m) => sectionKey(m[1] ?? m[2] ?? ""))),
    numbers: new Set([...text.matchAll(/^#{1,6}\s+([0-9]+(?:\.[0-9]+)*)\.?\s/gm)].map((m) => m[1] ?? "")),
  };
  sections.set(document, found);
  return found;
}
const quoted = /\\?"((?:[^"\\]|\\[^"])+)\\?"/;
let codeCitations: number = 0;
for (const file of codeRoots.flatMap((dir) => codeFiles(join(root, dir)))) {
  const text = readFileSync(file, "utf8").replace(/\n\s*(?:--|\/\/|\/-|\*|#)?\s*/g, " ");
  const titles = new RegExp(`\\b([A-Z][A-Z-]*\\.md),?\\s+(${quoted.source}(?:\\s*(?:,|;|and|or)\\s*${quoted.source})*)`, "g");
  for (const m of text.matchAll(titles)) {
    const [, document = "", list = ""] = m;
    const known = sectionsOf(document);
    if (known === undefined) { codeCitations++; fail(file, `cites missing document ${document}`); continue; }
    for (const t of list.matchAll(new RegExp(quoted.source, "g"))) {
      const title = t[1] ?? "";
      codeCitations++;
      if (!known.keys.has(sectionKey(title))) fail(file, `cites ${document}, "${title}", which it does not hold`);
    }
  }
  const numbered = /\b([A-Z][A-Z]+(?:-[A-Z]+)*)(?:\.md)?,?\s*((?:§\s*[0-9]+(?:\.[0-9]+)*(?:\s*[–-]\s*[0-9]+(?:\.[0-9]+)*)?(?:\s*(?:,|;|and|or)\s*(?=§))?)+)/g;
  for (const m of text.matchAll(numbered)) {
    const [, name = "", list = ""] = m;
    const known = sectionsOf(`${name}.md`);
    if (known === undefined) continue;
    for (const n of list.matchAll(/(?:§|[–-])\s*([0-9]+(?:\.[0-9]+)*)/g)) {
      codeCitations++;
      if (!known.numbers.has(n[1] ?? "")) fail(file, `cites ${name} §${n[1]}, which it does not number`);
    }
  }
}

// Annotations: the cheat sheet's entries, the first code span of each `###`
// heading of ANNOTATIONS.md (a tag `@name`, or an alias's name), are exactly
// the JSDoc tags the clause reader reads (`annotationTags`) and the type
// aliases the verifier's declaration file declares.
const cheatSheet = join(root, "docs", "ANNOTATIONS.md");
const declared = [...readFileSync(join(root, "tools", "resolvable.d.ts"), "utf8").matchAll(/^type (\w+)/gm)]
  .map((m) => m[1] ?? "");
const read = new Set([...annotationTags.map((t) => `@${t}`), ...declared]);
const entries = new Set([...withoutCode(readFileSync(cheatSheet, "utf8")).matchAll(/^### `(@?\w+)/gm)]
  .map((m) => m[1] ?? ""));
for (const a of read) if (!entries.has(a)) fail(cheatSheet, `has no entry for \`${a}\`, an annotation TScert reads`);
for (const e of entries) if (!read.has(e)) fail(cheatSheet, `has an entry for \`${e}\`, which no reader reads`);

for (const p of problems) process.stdout.write(`${p}\n`);
process.stdout.write(`docs: ${files.length} documents, ${codeCitations} citations in code, ${problems.length} problems\n`);
process.exitCode = problems.length ? 1 : 0;
