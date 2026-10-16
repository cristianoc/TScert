/* Commit records, parsed from a commit message and drawn as HTML. Pure: no
 * file system and no git; commit-records.mts reads git and calls it. A record's format is the `review`
 * skill's: a subject, sections ("Why:", "Rule added (name):", indented
 * blocks) and trailers. */

const esc = (s: string): string =>
  s.replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;").replace(/"/g, "&quot;");

const inline = (s: string): string => esc(s).replace(/`([^`]+)`/g, "<code>$1</code>");

type Section = { name: string; text: string[]; block: string[] };
export type CommitRecord = {
  sha: string; author: string; subject: string; sections: Section[];
  trailers: Map<string, string>; coauthors: string[]; stat: string[];
  examples: Map<string, Example>;
};
/** A pipeline case an Effect line names: its program at the commit, its kind
 * in `pipeline/cases.mts`, and the source span its expected diagnostic names. */
export type Example = { source: string; kind?: string; span?: [number, number] };

export type Group = { name: string; range?: string; records: CommitRecord[]; files: string[] };

const OUTCOMES: { [k: string]: string } = {
  verified: "ok", refused: "principled", gap: "gap", "no-behaviour-change": "neutral",
};
const FACTS = ["Parts", "Lean", "Wire", "Trust", "Depends", "Measured", "Tests"];

/** The trailers of a message: its last paragraph, when every line of it is
 * `Key: value` or a continuation line starting with a space, as
 * `git interpret-trailers --parse` reads it. A repeated key's values join. */
function parseTrailers(text: string): Map<string, string> {
  const trailers = new Map<string, string>();
  const paragraphs = text.trimEnd().split(/\n\s*\n/);
  const last = paragraphs.length > 1 ? paragraphs[paragraphs.length - 1].split("\n") : [];
  if (!last.length || !last.every(l => /^[A-Za-z0-9-]+: /.test(l) || /^\s/.test(l)) || /^\s/.test(last[0])) return trailers;
  const entries: [string, string][] = [];
  for (const l of last) {
    if (/^\s/.test(l)) entries[entries.length - 1][1] += ` ${l.trim()}`;
    else { const i = l.indexOf(":"); entries.push([l.slice(0, i).trim(), l.slice(i + 1).trim()]); }
  }
  for (const [key, value] of entries) trailers.set(key, trailers.has(key) ? `${trailers.get(key)} ${value}` : value);
  return trailers;
}

/** A commit's record from its text, with what git says of the commit. */
export function parseRecord(text: string, commit: { sha: string; author: string; stat: string[]; message: string;
    examples?: Map<string, Example> }): CommitRecord {
  const trailers = parseTrailers(text);
  const lines = text.trimEnd().split("\n");
  let end = lines.length;
  while (end > 1 && (/^[A-Za-z-]+: /.test(lines[end - 1]) || lines[end - 1].startsWith(" "))) end--;
  const sections: Section[] = [];
  let current: Section | undefined;
  for (const line of lines.slice(1, end)) {
    const head = /^([A-Z][A-Za-z]*(?: [a-z][A-Za-z]*){0,3}(?: \((?:[^()]|\([^()]*\))*\))?):\s*(.*)$/.exec(line);
    if (head) {
      current = { name: head[1], text: head[2] ? [head[2]] : [], block: [] };
      sections.push(current);
    } else if (/^ {2,}\S/.test(line)) {
      (current ??= pushProse(sections)).block.push(line);
    } else if (line.trim()) {
      if (!current || current.block.length) current = pushProse(sections);
      current.text.push(line.trim());
    } else if (current?.block.length) current.block.push("");
    else if (current && !current.name) current = undefined;
  }
  return {
    sha: commit.sha, author: commit.author, subject: lines[0], sections, trailers,
    coauthors: commit.message.split("\n").filter(l => l.startsWith("Co-Authored-By:"))
      .map(l => l.replace("Co-Authored-By:", "with").replace(/<[^>]*>/, "").trim()),
    stat: commit.stat, examples: commit.examples ?? new Map(),
  };
}


function pushProse(sections: Section[]): Section {
  const s = { name: "", text: [], block: [] };
  sections.push(s);
  return s;
}

const words = (r: CommitRecord, key: string): string[] => (r.trailers.get(key) ?? "").split(/\s+/).filter(Boolean);

function tests(value: string): string {
  return value.split(/\s+(?=[+-]|forged:)/).map(t => {
    const kind = t.startsWith("+") ? "pos" : t.startsWith("-") ? "neg" : t.startsWith("forged:") ? "forged" : "plain";
    return `<span class="test ${kind}">${esc(t.replace(/^[+-]|^forged:/, ""))}</span>`;
  }).join(" ");
}

/** Mathematics set as type theory sets it: one-letter names (variables,
 * metavariables) italic; a name applied to arguments, `sig(g)`, an upright
 * operator; a capitalised name an upright constructor; binders and relations
 * coloured; `code` in backticks highlighted TypeScript; a run of two or more
 * words, `g read, not called`, a side condition in text. `_x`, `_{…}` and
 * `^{…}` are sub- and superscripts. The input is the record's; nothing is
 * added to it. */
const KEYWORDS = new Set(["if", "then", "else", "let", "in", "tag"]);
const CONNECTIVES = new Set(["or", "and", "not"]);
/** JavaScript's literal values, drawn as code wherever they appear. */
const LITERALS = new Set(["null", "undefined", "true", "false", "NaN"]);
const BINDERS = new Set("∀∃λΛμ");
const RELATIONS = new Set("⊢⊨≤≥⊑⊒∈∉⊆⊂=≠≡:⇝↦≜≔");
const TEXT_WORD = /^(?:a|an|A|An|[A-Za-z][A-Za-z'-]*[a-z][A-Za-z'-]*)$/;
type MathToken = { kind: "code" | "str" | "intr" | "script" | "word" | "num" | "space" | "sym"; text: string };
function mathTokens(text: string): MathToken[] {
  const token = /(`[^`]+`)|("[^"\n]*"|%[A-Za-z][^%\s]*%)|(_\{[^{}]*\}|\^\{[^{}]*\}|_[A-Za-z0-9\u0370-\u03ff\u2200-\u22ff]+\u20d7?)|([A-Za-z\u0370-\u03ff][A-Za-z0-9\u0370-\u03ff'′-]*\u20d7?)|(\d+)|(\s+)|([\s\S])/g;
  return [...text.matchAll(token)].map(([t, code, str, script, word, num, space]) => ({
    kind: code ? "code" : str ? (str.startsWith("%") ? "intr" : "str") : script ? "script" : word ? "word" : num ? "num" : space ? "space" : "sym", text: t }));
}
/** What each token of a formula is: a word of a side condition (`text`),
 * code, a quoted string, a sub- or superscript, `refused`, a keyword, an
 * operator applied to arguments, a one-letter variable, a capitalised
 * constructor, a binder, a relation, or other symbols and spaces (`plain`). */
type MathRole = "text" | "code" | "str" | "intr" | "lit" | "script" | "refused" | "kw" | "op" | "var" | "con" | "bind" | "rel" | "plain";
function mathRoles(ts: MathToken[]): MathRole[] {
  // Side conditions in words: two or more words, or one lowercase word of
  // three letters or more, not applied to arguments; a run continues across
  // spaces, punctuation, quoted strings and code.
  const prose = new Set<number>();
  // A lone word just after a relation (`: bool`, `= number`) names a type.
  const afterRelation = (k: number) => { let j = k - 1; while (ts[j]?.kind === "space") j--; return ts[j] !== undefined && RELATIONS.has(ts[j].text); };
  const textWord = (k: number) => ts[k]?.kind === "word" && TEXT_WORD.test(ts[k].text) && !KEYWORDS.has(ts[k].text) && !LITERALS.has(ts[k].text)
    && ts[k + 1]?.text !== "(" && ts[k + 1]?.kind !== "script";
  // Inside a run a keyword is an ordinary word ("in double brackets").
  const joins = (k: number) => ["space", "code", "str"].includes(ts[k].kind) || ",;()".includes(ts[k].text)
    || (ts[k].kind === "word" && KEYWORDS.has(ts[k].text));
  for (let i = 0; i < ts.length; i++) {
    if (!textWord(i)) continue;
    const run = [i];
    for (let k = i + 1; k < ts.length && (joins(k) || textWord(k)); k++) if (textWord(k)) run.push(k);
    const last = run[run.length - 1];
    if (run.length >= 2 || (/^[a-z]{3,}$/.test(ts[i].text) && !afterRelation(i))) {
      // A trailing closing parenthesis or string belongs to the run when the run holds its start.
      // An opening parenthesis just before the run belongs to it too.
      const start = ts[i - 1]?.text === "(" ? i - 1 : i;
      let end = last;
      while (end + 1 < ts.length && (ts[end + 1].kind === "str" || (ts[end + 1].text === ")" && ts.slice(start, end + 1).some(t => t.text === "(")))) end++;
      for (let k = start; k <= end; k++) prose.add(k);
      i = end;
    }
  }
  return ts.map((t, i): MathRole => {
    if (t.kind === "code" || t.kind === "str" || t.kind === "intr" || t.kind === "script") return t.kind;
    if (t.text === "refused") return "refused";
    if (prose.has(i)) return "text";
    if (t.kind === "word") {
      const w = t.text;
      // A keyword ending a sentence ("beginning with") is a word of it.
      if (KEYWORDS.has(w)) return prose.has(i - 1 - Number(ts[i - 1]?.kind === "space")) ? "text" : "kw";
      if (LITERALS.has(w)) return "lit";
      if (CONNECTIVES.has(w)) return "text";
      if (/^[a-z]{3,}$/.test(w) && afterRelation(i)) return "con";
      if ((ts[i + 1]?.text === "(" || ts[i + 1]?.kind === "script") && w.length > 1) return "op";
      if (/^[A-Za-zͰ-Ͽ][0-9'′]*⃗?$/.test(w)) return "var";
      return /^[A-Z]/.test(w) ? "con" : "op";
    }
    if (t.kind === "sym") return BINDERS.has(t.text) ? "bind" : RELATIONS.has(t.text) ? "rel" : "plain";
    return "plain";
  });
}

function math(text: string): string {
  const ts = mathTokens(text), roles = mathRoles(ts);
  const prose = (i: number) => roles[i] === "text" || ((roles[i] === "code" || roles[i] === "str") && (roles[i - 1] === "text" || roles[i + 1] === "text"));
  const CLASS: { [R in MathRole]: string } = {
    text: "m-text", code: "", str: "", intr: "m-intr", lit: "m-lit", script: "", refused: "refused", kw: "m-kw", op: "m-op", var: "", con: "m-con", bind: "m-bind", rel: "m-rel", plain: "" };
  return ts.map((t, i) => {
    const e = esc(t.text), r = roles[i];
    const piece = r === "code" ? `<code class="m-code">${highlight(t.text.slice(1, -1))}</code>`
      : r === "str" ? `<code class="m-code"><span class="tk-s">${e}</span></code>`
      : r === "script" ? (() => {
          const sup = t.text.startsWith("^"), inner = t.text.replace(/^[_^]\{?|\}$/g, "");
          return `<${sup ? "sup" : "sub"}>${math(inner)}</${sup ? "sup" : "sub"}>`;
        })()
      : r === "var" ? `<var>${e}</var>`
      : CLASS[r] && r !== "text" ? `<span class="${CLASS[r]}">${e}</span>` : e;
    if (!prose(i)) return piece;
    return `${prose(i - 1) ? "" : '<span class="m-text">'}${piece}${prose(i + 1) ? "" : "</span>"}`;
  }).join("");
}

/** A line's parts: runs of three or more spaces separate side-by-side formulas. */
const parts = (line: string): string[] => line.trim().split(/\s{3,}/).filter(Boolean);

/** Formulas, one row per line, an indented line continuing the one above. */
const formulas = (lines: string[]): string =>
  `<div class="formulas">${lines.map(l => `<div class="row${/^\s{2,}/.test(l) ? " cont" : ""}">${parts(l).map(p => `<span>${math(p)}</span>`).join("")}</div>`).join("")}</div>`;

/** A `Rule:` block: groups separated by blank lines; a group with a line of
 * `─` is an inference rule (premises above, conclusion below, the name after
 * the bar); any other group is a list of formulas. The text is the record's. */
function rules(block: string[], kind = ""): string {
  const groups: string[][] = [[]];
  for (const line of block) {
    if (line.trim()) groups[groups.length - 1].push(line);
    else if (groups[groups.length - 1].length) groups.push([]);
  }
  return `<div class="rules">${groups.filter(g => g.length).map(g => {
    const bar = g.findIndex(l => /^\s*─{3,}/.test(l));
    if (bar < 0) return g.some(l => l.includes("⇝")) ? lowering(g, kind === "Typing") : formulas(g);
    const name = /\(([^()]+)\)\s*$/.exec(g[bar])?.[1] ?? "";
    // A definition ending in `=`, with its continuation, stays a formula above the rule.
    let first = 0;
    for (let i = 0; i < bar; i++) if (/=\s*$/.test(g[i])) first = i + 2;
    first = Math.min(first, bar);
    const above = g.slice(0, first);
    const premises = g.slice(first, bar).flatMap(parts);
    const conclusion = g.slice(bar + 1);
    return (above.length ? formulas(above) : "") +
      `<div class="infer"><div class="frac"><div class="premises">${premises.map(p => `<span>${math(p)}</span>`).join("")}</div>` +
      `<div class="bar"></div><div class="conclusion">${conclusion.map(l => `<div>${math(l.trim())}</div>`).join("")}</div></div>` +
      (name ? `<span class="rule-name">(${esc(name)})</span>` : "") + `</div>`;
  }).join("")}</div>`;
}

/** Lines without their common indentation. */
function dedent(lines: string[]): string[] {
  const indents = lines.filter(l => l.trim()).map(l => /^ */.exec(l)?.[0].length ?? 0);
  const cut = indents.length ? Math.min(...indents) : 0;
  const out = lines.map(l => l.slice(cut));
  while (out.length && !out[out.length - 1].trim()) out.pop();
  return out;
}

const TS_KEYWORDS = new Set(("abstract as async await break case catch class const constructor continue declare default delete do else " +
  "enum export extends false finally for from function get if implements import in instanceof interface keyof let new null of " +
  "private protected public readonly return set static super switch this throw true try type typeof undefined unique var void while yield").split(" "));

/** TypeScript or JavaScript source, highlighted by token. */
function highlight(code: string): string {
  const token = /(\/\/[^\n]*|\/\*[\s\S]*?\*\/)|("(?:[^"\\\n]|\\.)*"|'(?:[^'\\\n]|\\.)*'|`(?:[^`\\]|\\.)*`)|(\b\d[\d_.]*n?\b)|([A-Za-z_$][\w$]*)/g;
  let out = "", last = 0;
  for (const m of code.matchAll(token)) {
    out += esc(code.slice(last, m.index));
    const [t, comment, str, num, id] = m;
    out += comment !== undefined ? `<span class="tk-c">${esc(t)}</span>`
      : str !== undefined ? `<span class="tk-s">${esc(t)}</span>`
      : num !== undefined ? `<span class="tk-n">${esc(t)}</span>`
      : id !== undefined && TS_KEYWORDS.has(id) ? `<span class="tk-k">${esc(t)}</span>`
      : id !== undefined && /^[A-Z]/.test(id) ? `<span class="tk-t">${esc(t)}</span>`
      : esc(t);
    last = (m.index ?? 0) + t.length;
  }
  return out + esc(code.slice(last));
}

/** Code lines; `mark` names the lines the other version lacks. */
const codeBlock = (lines: string[], mark: "add" | "del" | "" = "", other: string[] = []): string =>
  `<pre class="code">${lines.map(l => `<span class="ln${mark && !other.includes(l) ? ` ${mark}` : ""}">${highlight(l) || " "}</span>`).join("")}</pre>`;

/** A change to a named object: `<Kind> <action> (<target>)`, the kind deciding
 * how its content is drawn (mathematics or code), Before/After shown side by side. */
const MATH_KINDS = new Set(["Rule", "Rules", "Semantics", "Definition", "Definitions", "Type", "Typing", "Notation"]);
const CODE_KINDS = new Set(["Example", "Counterexample", "Code"]);
/** Kinds whose lines are drawn as written: commands, layouts, aligned columns. */
const PLAIN_KINDS = new Set(["Tooling"]);

/** A lowering: each `source ⇝ target` line is the TypeScript form (highlighted)
 * mapped to its term in the calculus (operations coloured); `label: …` lines
 * are side conditions; a trailing parenthesized remark is a note. */
function lowering(lines: string[], typing = false): string {
  const term = (t: string): string =>
    math(t);
  const note = (t: string): [string, string] => {
    const m = /^(.*?)\s+(\([^()]*\))\s*$/.exec(t);
    return m ? [m[1], `<span class="note">${inline(m[2])}</span>`] : [t, ""];
  };
  return `<div class="lowering">${lines.filter(l => l.trim()).map(l => {
    const [body, remark] = note(l.trim());
    const arrow = body.indexOf("⇝");
    if (arrow >= 0) {
      const src = `<code class="src">${highlight(body.slice(0, arrow).trim())}</code>`;
      // A type's meaning is written ⟦source⟧ = type; a lowering, source ⇝ term.
      return typing
        ? `<div class="map"><span class="tgt sem">⟦${src}⟧</span><span class="to">=</span><span class="tgt">${term(body.slice(arrow + 1).trim())}</span>${remark}</div>`
        : `<div class="map">${src}<div class="result"><span class="to">⇝</span><span class="tgt">${term(body.slice(arrow + 1).trim())}</span>${remark}</div></div>`;
    }
    const lab = /^([a-z][\w ]{0,24}):\s+(.*)$/.exec(body);
    if (lab) return `<div class="cond"><span class="label">${esc(lab[1])}</span><span class="tgt">${term(lab[2])}</span>${remark}</div>`;
    return `<div class="cond"><span class="tgt">${term(body)}</span>${remark}</div>`;
  }).join("")}</div>`;
}

/** The program of an example, the span its diagnostic names marked. */
function program(e: Example): string {
  const [from, to] = e.span && e.span[1] <= e.source.length ? e.span : [e.source.length, e.source.length];
  const marked = highlight(e.source.slice(0, from)) +
    (to > from ? `<mark>${highlight(e.source.slice(from, to))}</mark>` : "") + highlight(e.source.slice(to));
  return `<pre class="code">${marked.trimEnd()}</pre>`;
}

/** An Effect line: `case   kind   old → new   reason`, three or more spaces
 * apart; ⚠ after the old outcome marks it unsound. A line naming a pipeline
 * case expands to the case's program at the commit. */
function effects(lines: string[], examples: Map<string, Example>): string {
  const KINDS = new Set(["positive", "negative", "gap", "control"]);
  return `<ul class="effect">${lines.filter(l => l.trim()).map(l => {
    const [what, ...rest] = parts(l);
    const example = examples.get(what);
    const kind = rest[0] !== undefined && KINDS.has(rest[0]) ? rest.shift() : example?.kind;
    const change = rest[0] !== undefined && rest[0].includes("→") ? rest.shift() ?? "" : "";
    const [old, now] = change.split("→").map(x => x.trim());
    const outcome = change
      ? `<span class="was${old.includes("⚠") ? " unsound" : ""}">${inline(old)}</span> <span class="arrow">→</span> <span class="now">${inline(now)}</span>`
      : "";
    const line = `<code>${esc(what)}</code>${kind ? ` <span class="kind ${esc(kind)}">${esc(kind)}</span>` : ""}` +
      (outcome ? ` ${outcome}` : "") + (rest.length ? ` <span class="why">${rest.map(inline).join(" ")}</span>` : "");
    return `<li>${example ? `<details><summary>${line}</summary>${program(example)}</details>` : line}</li>`;
  }).join("")}</ul>`;
}

function section(s: Section, examples: Map<string, Example> = new Map()): string {
  const m = /^([A-Z][A-Za-z]*)(?: (added|modified|removed|replaced))?(?: \(((?:[^()]|\([^()]*\))*)\))?$/.exec(s.name);
  const kind = m?.[1] ?? s.name, action = m?.[2] ?? "", target = m?.[3] ?? "";
  const lines = dedent(s.block);
  const head = s.name
    ? `<h4 class="change">${action ? `<span class="act ${action}">${action}</span>` : ""}${esc(kind)}${target && !CODE_KINDS.has(kind) ? ` <span class="target">${inline(target)}</span>` : ""}</h4>`
    : "";
  const text = s.text.length ? `<p>${inline(s.text.join(" "))}</p>` : "";
  if (!lines.length) return head + text;
  if (kind === "Effect") return head + text + effects(lines, examples);
  const split = lines.findIndex(l => /^(Before|After):\s*$/.test(l.trim()));
  const draw = (body: string[], mark: "add" | "del" | "" = "", other: string[] = []): string =>
    kind === "Lowering" ? lowering(body) : MATH_KINDS.has(kind) ? rules(body, kind) : CODE_KINDS.has(kind) ? codeBlock(body, mark, other)
    : PLAIN_KINDS.has(kind) ? `<pre class="code">${body.map(l => `<span class="ln">${esc(l) || " "}</span>`).join("")}</pre>`
    : `<div class="prose">${body.join("\n").split(/\n\s*\n/).map(p => `<p>${inline(p.replace(/\s+/g, " ").trim())}</p>`).join("")}</div>`;
  if (split < 0) return head + text + draw(lines);
  const before: string[] = [], after: string[] = [];
  let into: string[] | undefined;
  for (const l of lines) {
    const t = l.trim();
    if (t === "Before:") into = before;
    else if (t === "After:") into = after;
    else into?.push(l);
  }
  const b = dedent(before), a = dedent(after);
  return head + text + `<div class="versions">` +
    (b.length ? `<figure><figcaption>Before</figcaption>${draw(b, "del", a)}</figure>` : "") +
    (a.length ? `<figure><figcaption>After</figcaption>${draw(a, "add", b)}</figure>` : "") + `</div>`;
}

function card(r: CommitRecord): string {
  const outcome = r.trailers.get("Outcome") ?? "";
  const out: string[] = [
    `<article class="card" id="c-${r.sha}"><header><div><div class="sha">${r.sha} · ${esc(r.author)}</div>` +
    `<h3>${inline(r.subject)}</h3></div>` +
    (outcome ? `<span class="pill ${OUTCOMES[outcome] ?? "neutral"}">${esc(outcome)}</span>` : "") + `</header>`,
  ];
  const units = words(r, "Units");
  if (units.length) out.push(`<div class="units">${units.map(u => `<span>${esc(u)}</span>`).join("")}</div>`);
  for (const s of r.sections) out.push(section(s, r.examples));
  const facts = FACTS.flatMap(k => {
    const v = r.trailers.get(k);
    if (v === undefined) return [];
    const shown =
      k === "Parts" ? v.split(/\s+/).map(p => `<span class="chip${/semantics|trust|wire/.test(p) ? " strong" : ""}">${esc(p)}</span>`).join(" ")
      : k === "Tests" && /(^|\s)([+-]|forged:)/.test(v) ? tests(v)
      : k === "Trust" ? `<span class="${v === "none" ? "none" : "trust"}">${esc(v)}</span>`
      : inline(v.replace(/; /g, " · "));
    return `<dt>${k}</dt><dd>${shown}</dd>`;
  });
  if (facts.length) out.push(`<dl class="facts">${facts.join("")}</dl>`);
  const total = r.stat.at(-1);
  if (total !== undefined) {
    out.push(`<details><summary>${esc(total.trim())}</summary><pre class="code">${esc(r.stat.slice(0, -1).join("\n"))}</pre></details>`);
  }
  if (r.coauthors.length) out.push(`<div class="sha">${esc(r.coauthors.join(" · "))}</div>`);
  out.push("</article>");
  return out.join("\n");
}


function summary(groups: Group[]): string {
  const ranges = groups.filter(g => g.range);
  if (!ranges.length) return "";
  const items = ranges.map(g => {
    const count = (o: string) => g.records.filter(r => r.trailers.get("Outcome") === o).flatMap(r => words(r, "Units")).length;
    const units = ["verified", "refused", "gap"].map(o => [o, count(o)] as const).filter(([, n]) => n).map(([o, n]) => `${n} ${o}`).join(", ");
    const list = (key: string, skip = "") => [...new Set(g.records.map(r => r.trailers.get(key) ?? "").filter(v => v && v !== skip))];
    const parts = [...new Set(g.records.flatMap(r => words(r, "Parts")))];
    const facts = [
      `${g.records.length} commit${g.records.length === 1 ? "" : "s"}${units ? `, units ${units}` : ""}`,
      `parts: ${parts.map(p => `<span class="chip${/semantics|trust|wire/.test(p) ? " strong" : ""}">${esc(p)}</span>`).join(" ")}`,
      ...list("Trust", "none").map(t => `new trust: <span class="trust">${esc(t)}</span>`),
      ...list("Wire").map(w => `wire: ${inline(w)}`),
      ...list("Depends").map(d => `depends on: ${inline(d)}`),
    ];
    return `<li><a href="#g-${esc(g.name)}"><code>${esc(g.range ?? g.name)}</code></a><ul>${facts.map(f => `<li>${f}</li>`).join("")}</ul></li>`;
  });
  const owners = new Map<string, string[]>();
  for (const g of ranges) for (const f of g.files) owners.set(f, [...(owners.get(f) ?? []), g.name]);
  const shared = [...owners].filter(([, gs]) => gs.length > 1).sort();
  return `<section><h2>Branches</h2><ul class="summary">${items.join("")}</ul>` +
    (shared.length ? `<h4>Files changed by more than one branch</h4><ul class="summary">${shared.map(([f, gs]) => `<li><code>${esc(f)}</code>: ${gs.map(esc).join(", ")}</li>`).join("")}</ul>` : "") +
    `</section>`;
}

export const CSS = `
:root { --bg:#f6f7f5; --surface:#fff; --ink:#1d2422; --muted:#5b6662; --rule:#d9dedb; --accent:#1f6f66; --code-bg:#eef1ef; --math-bg:#f3f1ea;
  --ok:#2e7d4f; --ok-bg:#e3f2e8; --principled:#8a5a12; --principled-bg:#f6ecd9; --gap:#5e6870; --gap-bg:#e8ebed; --neutral:#2b5b9c; --neutral-bg:#e2eaf6;
  --trust:#8b2f4b; --trust-bg:#f6e3ea; --neg:#9a3a2a; --neg-bg:#f7e4df;
  --display:"IBM Plex Serif",Georgia,serif; --body:"IBM Plex Sans","Helvetica Neue",Arial,sans-serif; --mono:"IBM Plex Mono",Menlo,Consolas,monospace; --math:"STIX Two Text","STIX Two Math","STIXGeneral","Cambria Math","Apple Symbols",Georgia,serif; }
@media (prefers-color-scheme: dark) { :root:not([data-theme="light"]) { --bg:#131816; --surface:#1b2220; --ink:#e3e9e6; --muted:#9aa6a1; --rule:#2f3936; --accent:#6cc3b6; --code-bg:#222b28; --math-bg:#24231d;
  --ok:#7fd3a0; --ok-bg:#1f3428; --principled:#e3b46a; --principled-bg:#382c17; --gap:#aab4bb; --gap-bg:#2a3135; --neutral:#8fb3e8; --neutral-bg:#1e2a3d; --trust:#ec97b1; --trust-bg:#3a2029; --neg:#f0a493; --neg-bg:#3a221d; color-scheme:dark } }
:root[data-theme="dark"] { --bg:#131816; --surface:#1b2220; --ink:#e3e9e6; --muted:#9aa6a1; --rule:#2f3936; --accent:#6cc3b6; --code-bg:#222b28; --math-bg:#24231d;
  --ok:#7fd3a0; --ok-bg:#1f3428; --principled:#e3b46a; --principled-bg:#382c17; --gap:#aab4bb; --gap-bg:#2a3135; --neutral:#8fb3e8; --neutral-bg:#1e2a3d; --trust:#ec97b1; --trust-bg:#3a2029; --neg:#f0a493; --neg-bg:#3a221d; color-scheme:dark }
* { box-sizing:border-box } body { margin:0; background:var(--bg); color:var(--ink); font:15px/1.6 var(--body) }
main { max-width:900px; margin:0 auto; padding-inline:20px; padding-block:32px 64px; display:flex; flex-direction:column; gap:22px }
h1 { font:600 32px/1.15 var(--display); margin:0 } h2 { font:600 22px/1.2 var(--display); margin:12px 0 8px; padding-top:12px; border-top:2px solid var(--ink) }
h3 { font:600 19px/1.3 var(--display); margin:2px 0 0; text-wrap:balance }
h4 { font:600 11px/1 var(--body); letter-spacing:.08em; text-transform:uppercase; color:var(--muted); margin:12px 0 4px }
p { margin:2px 0; max-width:72ch } .lede { color:var(--muted) }
code { font:13px/1.5 var(--mono); background:var(--code-bg); padding:1px 4px; border-radius:3px }
pre { margin:4px 0; padding:12px 14px; border-radius:6px; overflow-x:auto }
pre.code { font:13px/1.55 var(--mono); background:var(--code-bg) }
.rules { display:flex; flex-direction:column; gap:14px; background:var(--math-bg); border-left:3px solid var(--accent); border-radius:6px; padding:14px 18px; overflow-x:auto; font:16px/1.6 var(--math) }
.rules sub, .rules sup { font-size:.72em; line-height:0 }
.formulas { display:flex; flex-direction:column; gap:4px }
.formulas .row { display:flex; flex-wrap:wrap; gap:4px 28px } .formulas .row.cont { padding-left:2em }
.infer { display:flex; align-items:center; gap:12px }
.frac { display:inline-flex; flex-direction:column; align-items:center; min-width:0 }
.premises { display:flex; flex-wrap:wrap; justify-content:center; gap:4px 26px; padding:0 6px 3px }
.bar { align-self:stretch; border-top:1.5px solid var(--ink) }
.conclusion { padding:3px 6px 0; text-align:center }
.rule-name { font:15px/1 var(--math); font-variant:small-caps; letter-spacing:.02em; color:var(--accent); white-space:nowrap }
.card { background:var(--surface); border:1px solid var(--rule); border-radius:8px; padding:20px 22px; display:flex; flex-direction:column; gap:6px; min-width:0 }
.card > header { display:flex; justify-content:space-between; gap:12px; align-items:flex-start }
.sha { font:12px/1.4 var(--mono); color:var(--muted) }
.pill { font:600 11px/1 var(--body); letter-spacing:.06em; text-transform:uppercase; padding:6px 9px; border-radius:99px; white-space:nowrap }
.pill.ok { color:var(--ok); background:var(--ok-bg) } .pill.principled { color:var(--principled); background:var(--principled-bg) }
.pill.gap { color:var(--gap); background:var(--gap-bg) } .pill.neutral { color:var(--neutral); background:var(--neutral-bg) }
.units { display:flex; flex-wrap:wrap; gap:6px } .units span { font:12px/1 var(--mono); border:1px solid var(--rule); border-radius:4px; padding:5px 7px }
dl.facts { display:grid; grid-template-columns:max-content minmax(0,1fr); gap:6px 16px; margin:12px 0 0; padding-top:12px; border-top:1px solid var(--rule); font-size:13.5px }
dt { font:600 11px/1.9 var(--body); letter-spacing:.06em; text-transform:uppercase; color:var(--muted) }
dd { margin:0; min-width:0; display:flex; flex-wrap:wrap; gap:5px; align-items:baseline }
.chip { font:500 12px/1 var(--body); border:1px solid var(--rule); border-radius:4px; padding:4px 7px } .chip.strong { color:var(--accent); border-color:var(--accent) }
.trust { color:var(--trust); background:var(--trust-bg); padding:2px 6px; border-radius:4px } .none { color:var(--muted) }
.test { font:12px/1 var(--mono); padding:4px 7px; border-radius:4px }
.test.pos { color:var(--ok); background:var(--ok-bg) } .test.pos::before { content:"✓ " }
.test.neg { color:var(--neg); background:var(--neg-bg) } .test.neg::before { content:"✗ " }
.test.forged { color:var(--principled); background:var(--principled-bg) } .test.forged::before { content:"forged " }
details { margin-top:8px; font-size:13px; color:var(--muted) } summary { cursor:pointer }
.table-wrap { overflow-x:auto; border:1px solid var(--rule); border-radius:8px; background:var(--surface) }
table { border-collapse:collapse; width:100%; font-size:13px } th, td { text-align:left; vertical-align:top; padding:8px 10px; border-bottom:1px solid var(--rule) }
th { font:600 11px/1.2 var(--body); letter-spacing:.06em; text-transform:uppercase; color:var(--muted); white-space:nowrap } td.num { font-variant-numeric:tabular-nums }
h4.change { display:flex; align-items:center; gap:8px; text-transform:none; letter-spacing:0; font:600 14px/1.3 var(--body); color:var(--ink); margin:16px 0 6px }
h4.change .target { font-weight:400; color:var(--muted) }
.act { font:600 10.5px/1 var(--body); letter-spacing:.06em; text-transform:uppercase; padding:4px 7px; border-radius:4px }
.act.added { color:var(--ok); background:var(--ok-bg) } .act.removed { color:var(--neg); background:var(--neg-bg) }
.act.modified, .act.replaced { color:var(--principled); background:var(--principled-bg) }
.versions { display:grid; grid-template-columns:minmax(0,1fr) minmax(0,1fr); gap:10px }
.versions figure { margin:0; min-width:0 } .versions figcaption { font:600 11px/1 var(--body); letter-spacing:.06em; text-transform:uppercase; color:var(--muted); margin:0 0 4px }
.versions .rules { height:calc(100% - 18px); box-sizing:border-box }
pre.code .ln { display:block; white-space:pre } pre.code .ln.add { background:var(--ok-bg) } pre.code .ln.del { background:var(--neg-bg) }
.tk-k { color:#8e3fb5 } .tk-s { color:#2b7a3d } .tk-n { color:#b0601a } .tk-c { color:var(--muted); font-style:italic } .tk-t { color:#2b5b9c }
.prose p { margin:4px 0 }
ul.effect, ul.summary { margin:4px 0; padding-left:20px } ul.effect li, ul.summary li { margin:3px 0 } ul.summary ul { padding-left:18px; color:var(--muted) }
ul.effect .arrow { color:var(--accent); font-weight:600 }
ul.effect details { margin:0; color:inherit; font-size:inherit } ul.effect summary { list-style-position:outside }
ul.effect .kind { font-size:11px; text-transform:uppercase; letter-spacing:.04em; padding:1px 6px; border-radius:4px; background:var(--chip, #eee) }
ul.effect .kind.negative { color:#8a3b12 } ul.effect .kind.positive { color:#22663a } ul.effect .kind.gap { color:#7a5b00 }
ul.effect .was.unsound { color:#b3261e; font-weight:600 } ul.effect .now { font-weight:500 } ul.effect .why { color:var(--muted) }
ul.effect mark { background:#ffe08a; color:inherit; border-radius:2px }
@media (max-width:720px) { .versions { grid-template-columns:minmax(0,1fr) } }
.lowering { display:flex; flex-direction:column; gap:6px; background:var(--math-bg); border-left:3px solid var(--accent); border-radius:6px; padding:12px 16px; overflow-x:auto }
.lowering .map, .lowering .cond, .lowering .result { display:flex; flex-wrap:wrap; align-items:baseline; gap:6px 10px }
.lowering .map:not(:has(.sem)) { flex-direction:column; align-items:stretch; gap:4px }
.lowering .result { display:grid; grid-template-columns:auto minmax(0,1fr); align-items:baseline; gap:2px 10px; padding-left:1em } .lowering .result .note { grid-column:2 }
.m-intr { font:14px/1.5 var(--mono); color:#2b5b9c } .m-lit { font:13px/1.5 var(--mono); color:#8e3fb5 }
.lowering code.src { font:13px/1.5 var(--mono); background:var(--surface); border:1px solid var(--rule); padding:2px 6px; border-radius:4px }
.lowering .to { color:var(--accent); font-weight:600; font-size:17px }
.lowering .tgt { font:16px/1.5 var(--math) } .rules .lowering { background:none; border:0; padding:0 } .lowering .sem code.src { margin:0 2px }
var { font-style:italic } .m-op { color:#2b5b9c; font-style:normal } .m-con { color:#1f6f66; font-style:normal; font-variant:small-caps }
.m-kw { color:#8e3fb5; font-weight:600; font-style:normal } .m-bind { color:#8e3fb5 } .m-rel { color:var(--accent); padding:0 .12em }
.m-text { font:14px/1.5 var(--body); color:var(--muted) } code.m-code { font:13px/1.5 var(--mono); background:var(--surface); border:1px solid var(--rule); padding:1px 5px; border-radius:4px }
.refused { color:var(--neg); font-weight:600 }
.lowering .refused { color:var(--neg); font-weight:600 }
.lowering .label { font:600 11px/1 var(--body); letter-spacing:.05em; text-transform:uppercase; color:var(--muted); min-width:7em }
.lowering .cond { padding-left:1.5em } .lowering .note { color:var(--muted); font:italic 13px/1.4 var(--body) }
a { color:var(--accent) } :focus-visible { outline:2px solid var(--accent); outline-offset:2px }
@media (max-width:520px) { dl.facts { grid-template-columns:minmax(0,1fr) } .card > header { flex-direction:column } }`;

/** The page's body: a summary of each range, then each range's cards. */
export function pageBody(groups: Group[]): string {
  const commits = groups.reduce((n, g) => n + g.records.length, 0);
  return `<main><header><h1>Commit Records</h1><p class="lede">${commits} commit${commits === 1 ? "" : "s"}, rendered from their records.</p></header>
${summary(groups)}
${groups.map(g => (g.range ? `<h2 id="g-${esc(g.name)}"><code>${esc(g.range)}</code></h2>` : "") + g.records.map(card).join("\n")).join("\n")}
</main>`;
}
