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
 * rule's declarations, and a page drawn as dev/record-render.mts draws records.
 */
import { execFileSync } from "node:child_process";
import { readFileSync, writeFileSync } from "node:fs";
import { join, resolve } from "node:path";
import { CSS, rules as ruleBlocks } from "./record-render.mts";
import { FACES } from "./style-tokens.mts";

const root: string = resolve(import.meta.dirname, "..");

/* ---- The rules' document, as the verifier exports it ---- */

export type RuleVar = "left" | "right" | "result";
export type Normalisation = "identity" | "shiftCount";
export type Coef = { lit: number; byConstant: number; byPower: number };
export type RuleFact = { terms: { var: RuleVar; coef: Coef }[]; bound: Coef };
export type Constant = { lower: number | null; upper: number | null; normalisation: Normalisation };
export type Sort = "Num" | "SafeInt";
export type Role = "operand" | "constant" | "result";
export type RuleVariable = { var: RuleVar; role: Role; sort: Sort; kind: Normalisation | null };
export type Rule = {
  name: string; declaration: string; proof: string; op: string; variables: RuleVariable[];
  constant: Constant | null; premises: RuleFact[]; conclusion: RuleFact[];
};
export type RulesDocument = { statement: string; soundness: string; rules: Rule[] };

/** A reading failure: the line and what it is not. */
function refuse(line: number, what: string): never {
  throw new Error(`the rules' document, line ${line}: ${what}`);
}

function integer(text: string, line: number): number {
  const n = Number(text);
  return /^-?\d+$/.test(text) && Number.isSafeInteger(n) ? n : refuse(line, `${text} is no safe integer`);
}

/** A coefficient: monomials `n`, `n·k`, `n·2^k`, a factor 1 written as its
 * sign, joined by ` + ` and ` - `. */
function coef(text: string, line: number): Coef {
  const c: Coef = { lit: 0, byConstant: 0, byPower: 0 };
  if (text === "0") return c;
  for (const m of text.replace(/ - /g, " + -").split(" + ")) {
    const unit = /^(-?)(?:(\d+)·)?(2\^k|k)$/.exec(m);
    if (unit !== null) {
      const n = (unit[1] === "-" ? -1 : 1) * (unit[2] === undefined ? 1 : integer(unit[2], line));
      if (unit[3] === "k") c.byConstant += n;
      else c.byPower += n;
    } else c.lit += integer(m, line);
  }
  return c;
}

function ruleVar(text: string, line: number): RuleVar {
  return text === "left" || text === "right" || text === "result" ? text : refuse(line, `${text} is no variable`);
}

/** A fact line, `` - `(a)·v + … ≤ b` ``. */
function fact(text: string, line: number): RuleFact {
  const m = /^- `(.*) ≤ (.*)`$/.exec(text);
  if (m === null || m[1] === undefined || m[2] === undefined) return refuse(line, "no fact");
  const terms = m[1].split(/ \+ (?=\()/).map((piece) => {
    const tm = /^\((.*)\)·(\w+)$/.exec(piece);
    if (tm === null || tm[1] === undefined || tm[2] === undefined) return refuse(line, `${piece} is no term`);
    return { var: ruleVar(tm[2], line), coef: coef(tm[1], line) };
  });
  return { terms, bound: coef(m[2], line) };
}

/** A variable's row of a rule's table. */
function variable(text: string, line: number): RuleVariable {
  const m = /^\| `(\w+)` \| ([^|]+) \| `(\w+)` \|$/.exec(text);
  if (m === null || m[1] === undefined || m[2] === undefined || m[3] === undefined) return refuse(line, "no variable row");
  const roles: { [r: string]: [Role, Normalisation | null] } = {
    "operand": ["operand", null], "result": ["result", null],
    "constant, a shift count": ["constant", "shiftCount"], "constant, read as itself": ["constant", "identity"],
  };
  const role = roles[m[2]];
  if (role === undefined) return refuse(line, `${m[2]} is no role`);
  const sort = m[3] === "Num" || m[3] === "SafeInt" ? m[3] : refuse(line, `${m[3]} is no sort`);
  return { var: ruleVar(m[1], line), role: role[0], sort, kind: role[1] };
}

/** The constant's sentence. */
function constant(text: string, line: number): Constant {
  const m = /^The constant: (no lower bound|at least (-?\d+)); (no upper bound|at most (-?\d+)); (read as itself|read as a shift count, modulo 32)\.$/.exec(text);
  if (m === null) return refuse(line, "no constant's sentence");
  return { lower: m[2] === undefined ? null : integer(m[2], line), upper: m[4] === undefined ? null : integer(m[4], line),
    normalisation: m[5] === "read as itself" ? "identity" : "shiftCount" };
}

/** **The rules' document from the verifier's Markdown**, line by line in the
 * form `RuleExport.rulesMarkdown` writes; any other line is refused. */
export function decodeRules(source: string): RulesDocument {
  const lines = source.split("\n");
  let at = 0;
  const peek = (): string => lines[at] ?? "";
  const next = (): string => lines[at++] ?? refuse(at, "the document ends early");
  const expect = (re: RegExp, what: string): RegExpExecArray => re.exec(next()) ?? refuse(at, `expected ${what}`);
  const blank = (): void => { if (next() !== "") refuse(at, "expected a blank line"); };
  expect(/^# Arithmetic rules$/, "the title"); blank();
  const intro = expect(/^The rules of `[\w.]+`, in the paper's order\. Each is sound by `([\w.]+)`, which `([\w.]+)` proves of every rule\.$/, "the soundness sentence");
  blank();
  expect(/^A fact is `Σ \(coefficient\)·variable ≤ bound`; `k` is the rule's constant as the rule reads it\.$/, "the facts' sentence");
  const rules: Rule[] = [];
  const facts = (title: string): RuleFact[] => {
    const head = next();
    if (head === `${title}: none.`) return [];
    if (head !== `${title}:`) refuse(at, `expected ${title}`);
    blank();
    const out: RuleFact[] = [];
    while (peek().startsWith("- ")) out.push(fact(next(), at));
    return out;
  };
  while (at < lines.length - 1) {
    blank();
    const name = expect(/^## (.+)$/, "a rule's heading")[1] ?? "";
    blank();
    const decl = expect(/^Operator `(\w+)`\. Stated by `([\w.]+)`, proved by `([\w.]+)`\.$/, "the rule's operator and declarations");
    blank();
    expect(/^\| Variable \| Role \| Sort \|$/, "the variables' table"); expect(/^\| --- \| --- \| --- \|$/, "the table's rule");
    const variables: RuleVariable[] = [];
    while (peek().startsWith("| ")) variables.push(variable(next(), at));
    blank();
    let c: Constant | null = null;
    if (peek().startsWith("The constant:")) { c = constant(next(), at); blank(); }
    const premises = facts("Premises");
    blank();
    const conclusion = facts("Conclusion");
    rules.push({ name, declaration: decl[2] ?? "", proof: decl[3] ?? "", op: decl[1] ?? "", variables, constant: c, premises, conclusion });
  }
  if (lines[at] !== "" || at !== lines.length - 1) refuse(at + 1, "text after the last rule");
  return { statement: intro[1] ?? "", soundness: intro[2] ?? "", rules };
}

/** The verifier's export of the arithmetic rules. */
function exportedRules(): RulesDocument {
  const verifier = join(root, "lean/.lake/build/bin/verifier");
  return decodeRules(execFileSync(verifier, ["--export", "rules", "arithmetic"], { encoding: "utf8" }));
}

/* ---- One renderer, three notations ---- */

/** How a notation sets the pieces of a rule. */
type Notation = {
  /** The name of a rule's result. */
  result: string;
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

/** A constant's letter by its kind, `d` for a shift count and `c` otherwise. */
const constantLetter = (c: Constant): string => (c.normalisation === "shiftCount" ? "d" : "c");
const boundName = (c: Constant, prime: string): string => (c.normalisation === "shiftCount" ? `d${prime}` : "c");

const LATEX: Notation = {
  result: "y", le: "\\le ", lt: "<", eq: "=", and: "\\wedge ", minus: "-", times: "\\,",
  power: (e) => `2^{${e}}`, bound: (c) => boundName(c, "'"),
  apply: (op, a, b) => {
    const symbol = operator(op, "latex");
    return `y=${a}${symbol}${/[A-Za-z]$/.test(symbol) ? " " : ""}${b}`;
  },
};
const MARKDOWN: Notation = {
  result: "r", le: "\\le ", lt: "<", eq: "=", and: ",\\ ", minus: "-", times: "\\,",
  power: (e) => `2^{${e}}`, bound: (c) => boundName(c, "'"),
  apply: (op, a, b) => `r\\leftarrow ${a}${operator(op, "markdown")}${b}`,
};
const TEXT: Notation = {
  result: "y", le: " ≤ ", lt: " < ", eq: " = ", and: ", ", minus: "−", times: "·",
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

const constantOf = (r: Rule): Constant | undefined => r.constant ?? undefined;

/** A rule's variable, as the export states it. */
function variableOf(r: Rule, x: RuleVar): RuleVariable {
  const v = r.variables.find((w) => w.var === x);
  if (v === undefined) throw new Error(`the rules' document: rule ${r.name} states no variable ${x}`);
  return v;
}

/** The letter of a variable by its role and sort, one convention for every
 * rule: an operand of `SafeInt` is `a` as the first operand and `b` as the
 * second, an operand of `Num` is `x`, a constant `d` as a shift count and
 * `c` otherwise, and the result the notation's. */
function letter(v: RuleVariable, notation: Notation): string {
  switch (v.role) {
    case "result": return notation.result;
    case "constant": return v.kind === "shiftCount" ? "d" : "c";
    case "operand": return v.sort === "Num" ? "x" : v.var === "left" ? "a" : "b";
  }
}

/** The slot of a rule's right operand: its letter as an operand of its sort. */
function slotOf(r: Rule): string {
  const v = variableOf(r, "right");
  return v.role === "constant" ? (v.sort === "Num" ? "x" : "b") : letter(v, MARKDOWN);
}

/** The names of a rule's variables. */
function names(r: Rule, notation: Notation): { [v in RuleVar]: string } {
  return { left: letter(variableOf(r, "left"), notation), right: letter(variableOf(r, "right"), notation),
    result: letter(variableOf(r, "result"), notation) };
}

/** The sorts of a rule's operands and constant, as the export states them;
 * those of one sort grouped, in the order left, right. */
function sorts(r: Rule, sort: (s: Sort) => string, of: string, sep: string): string {
  const groups: { names: string[]; sort: Sort }[] = [];
  for (const v of r.variables.filter((w) => w.role !== "result")) {
    const last = groups[groups.length - 1];
    const name = letter(v, LATEX);
    if (last !== undefined && last.sort === v.sort) last.names.push(name);
    else groups.push({ names: [name], sort: v.sort });
  }
  return groups.map((g) => `${g.names.join(",")}${of}${sort(g.sort)}`).join(sep);
}

/** The facts `int(v)` of a rule's operands and result of `SafeInt`. */
function ints(r: Rule, role: "operand" | "result", name: (v: RuleVariable) => string, int: (n: string) => string): string[] {
  return r.variables.filter((v) => v.role === role && v.sort === "SafeInt").map((v) => int(name(v)));
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
    const sorted = sorts(r, (s) => `\\mathit{${s}}`, ":", ",\\ ");
    return `${name} & ${sorted} & ${paperTriple(r)}`;
  }).join("\\\\[3pt]\n") + "\n";
}

/** A constant's side condition and normalisation, as premises. */
function constantPremises(c: Constant, notation: Notation): string[] {
  const bounds = [c.lower === null ? "" : `${literal(c.lower, notation)}${notation.le}`, constantLetter(c),
    c.upper === null ? "" : `${notation.lt}${literal(c.upper + 1, notation)}`].join("");
  const side = c.lower === null && c.upper === null ? [] : [bounds];
  return c.normalisation === "shiftCount" ? [...side, `${boundName(c, notation === TEXT ? "′" : "'")}${notation.eq}${constantLetter(c)}${notation === TEXT ? " mod " : "\\bmod "}32`] : side;
}

/** A rule as an inference in the notation of ARITHMETIC.md:
 * `int(a)`, `K ⊢ b = d`, the premises, over `K ⊢ r ← a op b ⊣ int(r), …`. */
function markdownRule(r: Rule): string {
  const c = constantOf(r);
  const k = c === undefined ? "" : MARKDOWN.bound(c);
  const n = names(r, MARKDOWN);
  const slot = slotOf(r);
  const above = [
    ...ints(r, "operand", (v) => (v.var === "right" ? slot : letter(v, MARKDOWN)), (x) => `\\mathrm{int}(${x})`),
    ...(r.constant === null ? []
      : [`K\\vdash ${slot}=${n.right}`, ...constantPremises(r.constant, MARKDOWN)]),
    ...conjunction(r.premises, n, k, MARKDOWN).map((p) => `K\\vdash ${p}`),
  ];
  const below = [...ints(r, "result", (v) => letter(v, MARKDOWN), (x) => `\\mathrm{int}(${x})`), ...conjunction(r.conclusion, n, k, MARKDOWN)];
  const sorted = sorts(r, (s) => `\\mathit{${s}}`, ":", ",\\ ");
  return `\\frac{${above.join("\\quad ")}}\n     {K\\vdash ${MARKDOWN.apply(r.op, n.left, slot)}\\dashv ${below.join(",\\ ")}}\n     \\ \\textsf{${r.name}}\\quad ${sorted}`;
}


/** ARITHMETIC.md's rules: each a comment naming the rule's declarations, then its `math` block. */
export function markdownRules(doc: RulesDocument): string {
  return doc.rules.map((r) => `<!-- ${r.declaration}, proved by ${r.proof} -->\n\n\`\`\`math\n${markdownRule(r)}\n\`\`\`\n`).join("\n");
}

/** A rule in the record notation dev/record-render.mts draws: premises,
 * a bar with the rule's name, the conclusion. */
function textRule(r: Rule): string[] {
  const c = constantOf(r);
  const k = c === undefined ? "" : TEXT.bound(c);
  const n = names(r, TEXT);
  const above = [
    sorts(r, (s) => s, " : ", ", "),
    ...ints(r, "operand", (v) => letter(v, TEXT), (x) => `int(${x})`),
    ...(r.constant === null ? [] : constantPremises(r.constant, TEXT)),
    ...conjunction(r.premises, n, k, TEXT),
  ];
  const below = [...ints(r, "result", (v) => letter(v, TEXT), (x) => `int(${x})`), ...conjunction(r.conclusion, n, k, TEXT)];
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
