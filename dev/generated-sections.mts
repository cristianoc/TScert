#!/usr/bin/env node
/**
 * Generated sections (docs/GENERATED-SECTIONS.md): text in the documents
 * that a producer computes from the code, between markers, and one path that
 * rewrites it or checks it.
 *
 *   node dev/generated-sections.mts            rewrite every section
 *   node dev/generated-sections.mts --check    write nothing; fail with the difference
 *   node dev/generated-sections.mts --page F   write the arithmetic rules' page to F
 *
 * A destination holds each section registered for it once, between
 * `<!-- generated: ID -->` and `<!-- end generated: ID -->` in Markdown, and
 * `% generated: ID` and `% end generated: ID` in LaTeX, each marker a line of
 * its own; a missing, duplicate, nested, unmatched or unregistered marker
 * fails. The text around the markers is left as it is.
 *
 * The arithmetic rules' producer is the verifier's export of
 * `ArithmeticRules.rules` (`verifier --export rules arithmetic`); one
 * renderer sets the rules in three notations: the paper's rule rows, the
 * `math` blocks of ARITHMETIC.md, each preceded by a comment carrying the
 * rule's JSON, and a page drawn as dev/record-render.mts draws records.
 */
import { execFileSync } from "node:child_process";
import { readFileSync, writeFileSync } from "node:fs";
import { join, resolve } from "node:path";
import { hasExactly, isParsedObject, type Json } from "../tools/calculus.mts";
import { CSS, rules as ruleBlocks } from "./record-render.mts";
import { FACES } from "./style-tokens.mts";

const root: string = resolve(import.meta.dirname, "..");

/* ---- The rules' document, as the verifier exports it ---- */

export type RuleVar = "left" | "right" | "result";
export type Domain = "safeInteger" | "number";
export type Normalisation = "identity" | "shiftCount";
export type Coef = { lit: number; byConstant: number; byPower: number };
export type RuleFact = { terms: { var: RuleVar; coef: Coef }[]; bound: Coef };
export type Constant = { symbol: string; lower: number | null; upper: number | null; normalisation: Normalisation };
export type Right = { operand: Domain } | { constant: Constant };
export type Rule = {
  name: string; declaration: string; proof: string; op: string;
  left: Domain; right: Right; premises: RuleFact[]; result: Domain; conclusion: RuleFact[];
};
export type RulesDocument = { statement: string; soundness: string; rules: Rule[] };

/** A decoding failure: the path of the value and what it is not. */
function refuse(path: string, what: string): never {
  throw new Error(`the rules' document: ${path} is not ${what}`);
}

/** An object holding exactly the keys `keys`. */
function object(v: Json | undefined, path: string, keys: readonly string[]): { [key: string]: Json } {
  if (!isParsedObject(v) || !hasExactly(v, keys)) return refuse(path, `an object of the fields ${keys.join(", ")}`);
  return v;
}

function text(v: Json | undefined, path: string): string {
  return typeof v === "string" ? v : refuse(path, "a string");
}

function integer(v: Json | undefined, path: string): number {
  return typeof v === "number" && Number.isSafeInteger(v) ? v : refuse(path, "a safe integer");
}

function list(v: Json | undefined, path: string): Json[] {
  return Array.isArray(v) ? v : refuse(path, "an array");
}

function domain(v: Json | undefined, path: string): Domain {
  return v === "safeInteger" || v === "number" ? v : refuse(path, "a domain");
}

function ruleVar(v: Json | undefined, path: string): RuleVar {
  return v === "left" || v === "right" || v === "result" ? v : refuse(path, "a rule variable");
}

function coef(v: Json | undefined, path: string): Coef {
  const o = object(v, path, ["lit", "byConstant", "byPower"]);
  return { lit: integer(o.lit, `${path}.lit`), byConstant: integer(o.byConstant, `${path}.byConstant`),
    byPower: integer(o.byPower, `${path}.byPower`) };
}

function fact(v: Json | undefined, path: string): RuleFact {
  const o = object(v, path, ["terms", "bound"]);
  return {
    terms: list(o.terms, `${path}.terms`).map((t, i) => {
      const term = object(t, `${path}.terms[${i}]`, ["var", "coef"]);
      return { var: ruleVar(term.var, `${path}.terms[${i}].var`), coef: coef(term.coef, `${path}.terms[${i}].coef`) };
    }),
    bound: coef(o.bound, `${path}.bound`),
  };
}

function optionalInteger(v: Json | undefined, path: string): number | null {
  return v === null ? null : integer(v, path);
}

function right(v: Json | undefined, path: string): Right {
  if (isParsedObject(v) && hasExactly(v, ["operand"])) return { operand: domain(v.operand, `${path}.operand`) };
  const o = object(v, path, ["constant"]);
  const c = object(o.constant, `${path}.constant`, ["symbol", "lower", "upper", "normalisation"]);
  const normalisation = c.normalisation === "identity" || c.normalisation === "shiftCount" ? c.normalisation
    : refuse(`${path}.constant.normalisation`, "a normalisation");
  return { constant: { symbol: text(c.symbol, `${path}.constant.symbol`), lower: optionalInteger(c.lower, `${path}.constant.lower`),
    upper: optionalInteger(c.upper, `${path}.constant.upper`), normalisation } };
}

function rule(v: Json | undefined, path: string): Rule {
  const o = object(v, path, ["name", "declaration", "proof", "op", "left", "right", "premises", "result", "conclusion"]);
  return {
    name: text(o.name, `${path}.name`), declaration: text(o.declaration, `${path}.declaration`),
    proof: text(o.proof, `${path}.proof`), op: text(o.op, `${path}.op`), left: domain(o.left, `${path}.left`),
    right: right(o.right, `${path}.right`),
    premises: list(o.premises, `${path}.premises`).map((f, i) => fact(f, `${path}.premises[${i}]`)),
    result: domain(o.result, `${path}.result`),
    conclusion: list(o.conclusion, `${path}.conclusion`).map((f, i) => fact(f, `${path}.conclusion[${i}]`)),
  };
}

/** The rules' document from its JSON text. */
export function decodeRules(source: string): RulesDocument {
  const parsed: Json = JSON.parse(source);
  const o = object(parsed, "the document", ["statement", "soundness", "rules"]);
  return { statement: text(o.statement, "statement"), soundness: text(o.soundness, "soundness"),
    rules: list(o.rules, "rules").map((r, i) => rule(r, `rules[${i}]`)) };
}

/** The verifier's export of the arithmetic rules. */
function exportedRules(): RulesDocument {
  const verifier = join(root, "lean/.lake/build/bin/verifier");
  return decodeRules(execFileSync(verifier, ["--export", "rules", "arithmetic"], { encoding: "utf8" }));
}

/* ---- One renderer, three notations ---- */

/** How a notation sets the pieces of a rule. */
type Notation = {
  /** The names of a rule's variables. */
  left: string; right: string; result: string;
  le: string; lt: string; eq: string; and: string; minus: string; times: string;
  power: (exponent: string) => string;
  /** The normalised constant's name: a shift count `d` reads `d'`. */
  bound: (c: Constant) => string;
  /** The operator applied to two operands, by the calculus's operator. */
  apply: (op: string, a: string, b: string) => string;
};

/** The operators' symbols, keyed by the calculus's operator names. */
const OPERATORS: { [op: string]: { latex: string; markdown: string; text: string } } = {
  shr: { latex: "\\gg", markdown: "\\mathbin{\\texttt{>>}}", text: ">>" },
  shl: { latex: "\\ll", markdown: "\\mathbin{\\texttt{<<}}", text: "<<" },
  ushr: { latex: "\\ggg", markdown: "\\mathbin{\\texttt{>>>}}", text: ">>>" },
  bitAnd: { latex: "\\mathbin{\\&}", markdown: "\\mathbin{\\&}", text: "&" },
  bitOr: { latex: "\\mathbin{|}", markdown: "\\mathbin{|}", text: "|" },
  xor: { latex: "\\mathbin{\\hat{}}", markdown: "\\mathbin{\\hat{}}", text: "^" },
  add: { latex: "+", markdown: "+", text: "+" },
  sub: { latex: "-", markdown: "-", text: "-" },
  mul: { latex: "*", markdown: "*", text: "*" },
};

function operator(op: string, notation: "latex" | "markdown" | "text"): string {
  const symbol = OPERATORS[op];
  if (symbol === undefined) throw new Error(`the rules' document: no symbol for the operator ${op}`);
  return symbol[notation];
}

const boundName = (c: Constant, prime: string): string => (c.normalisation === "shiftCount" ? `${c.symbol}${prime}` : c.symbol);

const LATEX: Notation = {
  left: "x", right: "x'", result: "y", le: "\\le ", lt: "<", eq: "=", and: "\\wedge ", minus: "-", times: "\\,",
  power: (e) => `2^{${e}}`, bound: (c) => boundName(c, "'"),
  apply: (op, a, b) => {
    const symbol = operator(op, "latex");
    return `y=${a}${symbol}${/[A-Za-z]$/.test(symbol) ? " " : ""}${b}`;
  },
};
const MARKDOWN: Notation = {
  left: "a", right: "b", result: "r", le: "\\le ", lt: "<", eq: "=", and: ",\\ ", minus: "-", times: "\\,",
  power: (e) => `2^{${e}}`, bound: (c) => boundName(c, "'"),
  apply: (op, a, b) => `r\\leftarrow ${a}${operator(op, "markdown")}${b}`,
};
const TEXT: Notation = {
  left: "x", right: "x′", result: "y", le: " ≤ ", lt: " < ", eq: " = ", and: ", ", minus: "−", times: "·",
  power: (e) => `2^{${e}}`, bound: (c) => boundName(c, "′"),
  apply: (op, a, b) => `\`y = ${a} ${operator(op, "text")} ${b}\``,
};

/** A signed summand of a side: its magnitude's text and its sign. */
type Summand = { negative: boolean; text: string };

/** The text of a power of two `2^p` with `p ≥ 8`, or of `2^p − 1`. */
function literal(n: number, notation: Notation): string {
  for (let p = 8; p <= 53; p++) {
    if (n === 2 ** p) return notation.power(String(p));
    if (n === 2 ** p - 1) return `${notation.power(String(p))}${notation.minus}1`;
  }
  return String(n);
}

/** A coefficient's summands: its literal part, its multiple of the bound
 * constant and its multiple of `2^bound`. */
function coefSummands(c: Coef, k: string, notation: Notation): Summand[] {
  const parts: Summand[] = [];
  const add = (n: number, unit: string): void => {
    if (n === 0) return;
    const magnitude = Math.abs(n);
    const body = unit === "" ? literal(magnitude, notation) : magnitude === 1 ? unit : `${magnitude}${notation.times}${unit}`;
    parts.push({ negative: n < 0, text: body });
  };
  add(c.byPower, notation.power(k));
  add(c.byConstant, k);
  add(c.lit, "");
  return parts;
}

/** A sum of summands; `0` when empty. */
function sum(parts: Summand[], notation: Notation): string {
  if (parts.length === 0) return "0";
  return parts.map((p, i) => (i === 0 ? (p.negative ? notation.minus : "") + p.text
    : `${p.negative ? notation.minus : "+"}${p.text}`)).join("");
}

/** One side of a fact: a relation's operands. */
type Inequality = { left: string; strict: boolean; right: string };

/** A fact `Σ aᵢ·vᵢ ≤ b` set as its positive terms bounded by its negative
 * ones and the bound: `-b ≤ N` where it has no positive term, and `P < B`
 * for a bound `B − 1` that is a power of two. */
function inequality(f: RuleFact, names: { [v in RuleVar]: string }, k: string, notation: Notation): Inequality {
  const positive: Summand[] = [];
  const negative: Summand[] = [];
  for (const t of f.terms) {
    const c = coefSummands(t.coef, k, notation);
    const sign = c.length === 1 && c[0] !== undefined && c[0].negative;
    const magnitude = c.length === 1 && c[0] !== undefined ? c[0].text : `(${sum(c, notation)})`;
    const termText = magnitude === "1" ? names[t.var]
      : `${magnitude}${/[0-9)]$/.test(magnitude) || notation === TEXT ? notation.times : ""}${names[t.var]}`;
    (sign ? negative : positive).push({ negative: false, text: termText });
  }
  const bound = coefSummands(f.bound, k, notation);
  if (positive.length === 0) {
    return { left: sum(bound.map((b) => ({ negative: !b.negative, text: b.text })), notation), strict: false,
      right: sum(negative, notation) };
  }
  const only = bound.length === 1 ? bound[0] : undefined;
  const strict = negative.length === 0 && only !== undefined && !only.negative && f.bound.byConstant === 0 &&
    f.bound.byPower === 0 && Number.isInteger(Math.log2(f.bound.lit + 1)) && f.bound.lit + 1 >= 256;
  const rightSide = strict ? literal(f.bound.lit + 1, notation) : sum([...negative, ...bound], notation);
  return { left: sum(positive, notation), strict, right: rightSide };
}

/** Facts set as a conjunction: an equality where two facts bound each
 * other, and a chain `A ≤ X ≤ B` where one fact's right side is the next
 * one's left and no other fact names `X`. */
function conjunction(facts: RuleFact[], names: { [v in RuleVar]: string }, k: string, notation: Notation): string[] {
  const parts = facts.map((f) => inequality(f, names, k, notation));
  const out: string[] = [];
  const elsewhere = (side: string, i: number): boolean =>
    parts.some((p, j) => j !== i && j !== i + 1 && (p.left === side || p.right === side));
  for (let i = 0; i < parts.length; i++) {
    const a = parts[i];
    if (a === undefined) continue;
    const b = parts[i + 1];
    const rel = (x: Inequality): string => (x.strict ? notation.lt : notation.le);
    if (b !== undefined && !a.strict && !b.strict && a.left === b.right && a.right === b.left) {
      out.push(`${a.left}${notation.eq}${a.right}`);
      i++;
    } else if (b !== undefined && a.right === b.left && !elsewhere(a.right, i)) {
      out.push(`${a.left}${rel(a)}${a.right}${rel(b)}${b.right}`);
      i++;
    } else out.push(`${a.left}${rel(a)}${a.right}`);
  }
  return out;
}

const constantOf = (r: Rule): Constant | undefined => ("constant" in r.right ? r.right.constant : undefined);

function names(r: Rule, notation: Notation): { [v in RuleVar]: string } {
  const c = constantOf(r);
  return { left: notation.left, right: c === undefined ? notation.right : c.symbol, result: notation.result };
}

/** The sorts of a rule's operands: `Num` for any number, `SafeInt` for a
 * safe integer, a constant being a safe integer; operands of one sort
 * grouped, in the order left, right. */
function sorts(r: Rule, variables: { left: string; right: string },
    sort: (s: "Num" | "SafeInt") => string, of: string, sep: string): string {
  const c = constantOf(r);
  const right: Domain = c === undefined && "operand" in r.right ? r.right.operand : "safeInteger";
  const vars: [string, "Num" | "SafeInt"][] = [
    [variables.left, r.left === "number" ? "Num" : "SafeInt"],
    [c === undefined ? variables.right : c.symbol, right === "number" ? "Num" : "SafeInt"],
  ];
  const groups: { names: string[]; sort: "Num" | "SafeInt" }[] = [];
  for (const [name, s] of vars) {
    const last = groups[groups.length - 1];
    if (last !== undefined && last.sort === s) last.names.push(name);
    else groups.push({ names: [name], sort: s });
  }
  return groups.map((g) => `${g.names.join(",")}${of}${sort(g.sort)}`).join(sep);
}

/** The rule's triple in the paper's notation, `{P} y = x op c {Q}`. */
function paperTriple(r: Rule): string {
  const c = constantOf(r);
  const k = c === undefined ? "" : LATEX.bound(c);
  const n = names(r, LATEX);
  const pre = conjunction(r.premises, n, k, LATEX);
  const post = conjunction(r.conclusion, n, k, LATEX);
  return `\\hoare{${pre.length === 0 ? "\\kw{true}" : pre.join(LATEX.and)}}{${LATEX.apply(r.op, n.left, n.right)}}{${post.join(LATEX.and)}}`;
}

/** The paper's rule rows: one row per triple, its operands' sorts, then the
 * triple; the rule's name on its first triple's row. */
export function paperRows(doc: RulesDocument): string {
  return doc.rules.map((r, i) => {
    const name = i > 0 && doc.rules[i - 1]?.name === r.name ? "" : `\\textsc{${r.name}}`;
    const sorted = sorts(r, { left: LATEX.left, right: LATEX.right }, (s) => `\\mathit{${s}}`, ":", ",\\ ");
    return `${name} & ${sorted} & ${paperTriple(r)}`;
  }).join("\\\\[3pt]\n") + "\n";
}

/** A constant's side condition and normalisation, as premises. */
function constantPremises(c: Constant, notation: Notation): string[] {
  const bounds = [c.lower === null ? "" : `${literal(c.lower, notation)}${notation.le}`, c.symbol,
    c.upper === null ? "" : `${notation.lt}${literal(c.upper + 1, notation)}`].join("");
  const side = c.lower === null && c.upper === null ? [] : [bounds];
  return c.normalisation === "shiftCount" ? [...side, `${boundName(c, notation === TEXT ? "′" : "'")}${notation.eq}${c.symbol}${notation === TEXT ? " mod " : "\\bmod "}32`] : side;
}

/** A rule as an inference in the notation of ARITHMETIC.md:
 * `int(a)`, `K ⊢ b = d`, the premises, over `K ⊢ r ← a op b ⊣ int(r), …`. */
function markdownRule(r: Rule): string {
  const c = constantOf(r);
  const k = c === undefined ? "" : MARKDOWN.bound(c);
  const n = names(r, MARKDOWN);
  n.right = notationRight(r, MARKDOWN);
  const above = [
    ...(r.left === "safeInteger" ? [`\\mathrm{int}(${n.left})`] : []),
    ...("operand" in r.right ? (r.right.operand === "safeInteger" ? [`\\mathrm{int}(${MARKDOWN.right})`] : [])
      : [`K\\vdash ${MARKDOWN.right}=${r.right.constant.symbol}`, ...constantPremises(r.right.constant, MARKDOWN)]),
    ...conjunction(r.premises, n, k, MARKDOWN).map((p) => `K\\vdash ${p}`),
  ];
  const below = [...(r.result === "safeInteger" ? [`\\mathrm{int}(${n.result})`] : []), ...conjunction(r.conclusion, n, k, MARKDOWN)];
  const sorted = sorts(r, { left: MARKDOWN.left, right: MARKDOWN.right }, (s) => `\\mathit{${s}}`, ":", ",\\ ");
  return `\\frac{${above.join("\\quad ")}}\n     {K\\vdash ${MARKDOWN.apply(r.op, n.left, MARKDOWN.right)}\\dashv ${below.join(",\\ ")}}\n     \\ \\textsf{${r.name}}\\quad ${sorted}`;
}

/** In ARITHMETIC.md a constant operand is the slot `b` the knowledge states
 * equal to the constant; the facts name the constant. */
function notationRight(r: Rule, notation: Notation): string {
  const c = constantOf(r);
  return c === undefined ? notation.right : c.symbol;
}

/** ARITHMETIC.md's rules: each a comment with the rule's JSON, then its `math` block. */
export function markdownRules(doc: RulesDocument): string {
  return doc.rules.map((r) => `<!-- ${JSON.stringify(r)} -->\n\n\`\`\`math\n${markdownRule(r)}\n\`\`\`\n`).join("\n");
}

/** A rule in the record notation dev/record-render.mts draws: premises,
 * a bar with the rule's name, the conclusion. */
function textRule(r: Rule): string[] {
  const c = constantOf(r);
  const k = c === undefined ? "" : TEXT.bound(c);
  const n = names(r, TEXT);
  const above = [
    sorts(r, { left: TEXT.left, right: TEXT.right }, (s) => s, " : ", ", "),
    ...(r.left === "safeInteger" ? [`int(${n.left})`] : []),
    ...("operand" in r.right ? (r.right.operand === "safeInteger" ? [`int(${TEXT.right})`] : []) : constantPremises(r.right.constant, TEXT)),
    ...conjunction(r.premises, n, k, TEXT),
  ];
  const below = [...(r.result === "safeInteger" ? [`int(${n.result})`] : []), ...conjunction(r.conclusion, n, k, TEXT)];
  return [above.length === 0 ? "true" : above.join("   "), `──────── (${r.name})`, `${TEXT.apply(r.op, n.left, n.right)} ⊣ ${below.join(", ")}`];
}

const esc = (s: string): string => s.replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;");

/** The rules' page: each rule drawn as a record's rule, with its declarations. */
export function rulesPage(doc: RulesDocument): string {
  const cards = doc.rules.map((r) => `<section class="card"><h3>${esc(r.name)}</h3>${ruleBlocks(textRule(r))}
<dl class="facts"><dt>Rule</dt><dd><code>${esc(r.declaration)}</code></dd><dt>Proof</dt><dd><code>${esc(r.proof)}</code></dd></dl></section>`);
  return `<!doctype html>
<html><head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">
<title>Arithmetic Rules</title>
${Object.values(FACES).map((f) => `<link rel="stylesheet" href="${f.href}">`).join("")}
<style>${CSS}</style></head><body><main><header><h1>Arithmetic Rules</h1>
<p class="lede">The rules of <code>ArithmeticRules.rules</code>, each sound by <code>${esc(doc.soundness)}</code> (the statement <code>${esc(doc.statement)}</code>).</p></header>
${cards.join("\n")}
</main></body></html>
`;
}

/* ---- The registry and the markers ---- */

export type Format = "markdown" | "latex";
export type Section = { id: string; destination: string; format: Format; produce: () => string };

/** Each producer's document, computed once per run. */
let rulesDocument: RulesDocument | undefined;
function arithmeticRules(): RulesDocument {
  rulesDocument ??= exportedRules();
  return rulesDocument;
}

/** The generated sections, each with its destination, format and producer. */
export const registry: readonly Section[] = [
  { id: "paper-arithmetic-rules", destination: "docs/drafts/tolerant-frames-note/note.tex", format: "latex",
    produce: (): string => paperRows(arithmeticRules()) },
  { id: "arithmetic-rules", destination: "docs/ARITHMETIC.md", format: "markdown",
    produce: (): string => markdownRules(arithmeticRules()) },
];

/** A marker line of a format: its kind and its section's identity. */
function marker(line: string, format: Format): { end: boolean; id: string } | null {
  const m = format === "latex" ? /^% (end )?generated: (\S+)$/.exec(line.trim())
    : /^<!-- (end )?generated: (\S+) -->$/.exec(line.trim());
  return m === null || m[2] === undefined ? null : { end: m[1] !== undefined, id: m[2] };
}

/** The spans of a destination's sections: each section's first and last
 * line inside its markers, by identity. */
export function spans(source: string, format: Format, file: string): Map<string, { start: number; end: number }> {
  const lines = source.split("\n");
  const found = new Map<string, { start: number; end: number }>();
  let open: { id: string; line: number } | null = null;
  lines.forEach((line, i) => {
    const m = marker(line, format);
    if (m === null) return;
    if (!m.end) {
      if (open !== null) throw new Error(`${file}:${i + 1}: section ${m.id} begins inside section ${open.id}`);
      if (found.has(m.id)) throw new Error(`${file}:${i + 1}: section ${m.id} appears twice`);
      open = { id: m.id, line: i };
    } else {
      if (open === null || open.id !== m.id) throw new Error(`${file}:${i + 1}: the end of section ${m.id} closes no such section`);
      found.set(m.id, { start: open.line + 1, end: i });
      open = null;
    }
  });
  if (open !== null) {
    const unclosed: { id: string; line: number } = open;
    throw new Error(`${file}:${unclosed.line + 1}: section ${unclosed.id} is not closed`);
  }
  return found;
}

/** A destination with its sections' text replaced by what their producers give. */
export function rewrite(source: string, format: Format, file: string, sections: readonly Section[]): string {
  const found = spans(source, format, file);
  for (const [id, span] of found) {
    if (!sections.some((s) => s.id === id)) throw new Error(`${file}:${span.start}: section ${id} is registered for no producer here`);
  }
  let lines = source.split("\n");
  for (const s of sections) {
    const span = spans(lines.join("\n"), format, file).get(s.id);
    if (span === undefined) throw new Error(`${file}: section ${s.id} has no markers`);
    const produced = s.produce().replace(/\n$/, "").split("\n");
    lines = [...lines.slice(0, span.start), ...produced, ...lines.slice(span.end)];
  }
  return lines.join("\n");
}

/** The first lines where two texts differ, as a short difference. */
function difference(file: string, was: string, now: string): string {
  const a = was.split("\n");
  const b = now.split("\n");
  let i = 0;
  while (i < a.length && i < b.length && a[i] === b[i]) i++;
  const shown = (xs: string[], sign: string): string[] => xs.slice(i, i + 6).map((l) => `${sign} ${l}`);
  return [`${file}:${i + 1}: the generated text differs`, ...shown(a, "-"), ...shown(b, "+")].join("\n");
}

/** Rewrite or check every destination: the differences found. */
export function run(check: boolean): string[] {
  const destinations = [...new Set(registry.map((s) => s.destination))];
  const differences: string[] = [];
  for (const destination of destinations) {
    const sections = registry.filter((s) => s.destination === destination);
    const formats = [...new Set(sections.map((s) => s.format))];
    const format = formats[0];
    if (format === undefined || formats.length > 1) {
      throw new Error(`${destination}: its sections are registered in the formats ${formats.join(", ")}; a destination has one format`);
    }
    const path = join(root, destination);
    const source = readFileSync(path, "utf8");
    const now = rewrite(source, format, destination, sections);
    if (now === source) continue;
    if (check) differences.push(difference(destination, source, now));
    else writeFileSync(path, now);
  }
  return differences;
}

if (import.meta.main) {
  const args = process.argv.slice(2);
  const pageAt = args.indexOf("--page");
  if (pageAt >= 0) {
    const out = args[pageAt + 1];
    if (out === undefined) throw new Error("usage: --page <file.html>");
    writeFileSync(out, rulesPage(arithmeticRules()));
    console.log(out);
  } else {
    const check = args.includes("--check");
    const differences = run(check);
    for (const d of differences) process.stderr.write(`${d}\n`);
    if (differences.length > 0) process.exit(1);
    console.log(check ? "generated sections: as their producers give them" : "generated sections: rewritten");
  }
}
