#!/usr/bin/env node
/**
 * Generated sections (docs/GENERATED-SECTIONS.md): text in the documents
 * that a producer computes from the code, between markers, and one path that
 * rewrites it or checks it.
 *
 *   node dev/generated-sections.mts            rewrite every section
 *   node dev/generated-sections.mts --check    write nothing; fail with the difference
 *   node dev/generated-sections.mts --page F   write the step rules' page to F
 *
 * A destination holds each section registered for it once, between
 * `<!-- generated: ID -->` and `<!-- end generated: ID -->` in Markdown, and
 * `% generated: ID` and `% end generated: ID` in LaTeX, each marker a line of
 * its own; a missing, duplicate, nested, unmatched or unregistered marker
 * fails. The text around the markers is left as it is.
 *
 * The step rules' producer is the verifier's export of
 * `ArithmeticRules.rules` (`verifier --export rules arithmetic`); one
 * renderer sets the rules of each of the paper's displays in three
 * notations: the paper's rule rows, the `math` blocks of the implementation's
 * documents, each preceded by a comment carrying the rule's declaration and
 * evidence, and a page drawn as dev/record-render.mts draws records.
 */
import { execFileSync } from "node:child_process";
import { readFileSync, writeFileSync } from "node:fs";
import { join, resolve } from "node:path";
import { CSS, rules as ruleBlocks } from "./record-render.mts";
import { FACES } from "./style-tokens.mts";

const root: string = resolve(import.meta.dirname, "..");

/* ---- The rules' document, as the verifier exports it ---- */

export type Base = "left" | "right" | "third" | "result";
/** A fact's term: a variable's value, or its length `|x|` where `len`. */
export type Term = { var: Base; len: boolean };
export type Normalisation = "identity" | "shiftCount";
export type Coef = { lit: number; byConstant: number; byPower: number };
export type RuleFact = { terms: { term: Term; coef: Coef }[]; bound: Coef };
export type Constant = { lower: number | null; upper: number | null; normalisation: Normalisation };
export type Sort = "Num" | "SafeInt" | "String" | "Array" | "TypedArray";
export type Role = "operand" | "index" | "written" | "constant" | "result";
export type RuleVariable = { var: Base; role: Role; sort: Sort; kind: Normalisation | null };
export type Display = "arithmetic" | "strings" | "views";
export type Atom =
  | { kind: "elem"; coll: Term; index: Term; value: Term; converted: boolean }
  | { kind: "kept"; coll: Term; index: Term };
export type Region = { kind: "st" | "vw" | "val" } | { kind: "spine" | "cells" | "fields"; of: Term } | { kind: "field"; of: Term; field: string };
export type Change = "keep" | "init" | "scalar" | "grow" | "any";
export type Evidence = { kind: "proved"; proof: string } | { kind: "assumed"; contracts: string[] };
export type Rule = {
  name: string; declaration: string; evidence: Evidence; op: string; display: Display; variables: RuleVariable[];
  constant: Constant | null; premises: RuleFact[]; conclusion: RuleFact[]; atoms: Atom[];
  effect: { region: Region; change: Change }[];
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

function base(text: string, line: number): Base {
  return text === "left" || text === "right" || text === "third" || text === "result" ? text
    : refuse(line, `${text} is no variable`);
}

/** A term: a variable, or its length `|variable|`. */
function term(text: string, line: number): Term {
  const m = /^\|(\w+)\|$/.exec(text);
  return m !== null && m[1] !== undefined ? { var: base(m[1], line), len: true } : { var: base(text, line), len: false };
}

const TERM = "\\w+|\\|\\w+\\|";

/** A fact line, `` - `(a)·t + … ≤ b` ``. */
function fact(text: string, line: number): RuleFact {
  const m = /^- `(.*) ≤ (.*)`$/.exec(text);
  if (m === null || m[1] === undefined || m[2] === undefined) return refuse(line, "no fact");
  const terms = m[1].split(/ \+ (?=\()/).map((piece) => {
    const tm = new RegExp(`^\\((.*)\\)·(${TERM})$`).exec(piece);
    if (tm === null || tm[1] === undefined || tm[2] === undefined) return refuse(line, `${piece} is no term`);
    return { term: term(tm[2], line), coef: coef(tm[1], line) };
  });
  return { terms, bound: coef(m[2], line) };
}

/** An atom line: `` - `x[i] ≐ y` ``, `` - `x[i] ≐ conv(v)` `` or `` - `kept x ≠ i` ``. */
function atom(text: string, line: number): Atom {
  const e = new RegExp(`^- \`(${TERM})\\[(${TERM})\\] ≐ (?:conv\\((${TERM})\\)|(${TERM}))\`$`).exec(text);
  if (e !== null && e[1] !== undefined && e[2] !== undefined) {
    const value = e[3] ?? e[4] ?? refuse(line, "no atom's value");
    return { kind: "elem", coll: term(e[1], line), index: term(e[2], line), value: term(value, line), converted: e[3] !== undefined };
  }
  const k = new RegExp(`^- \`kept (${TERM}) ≠ (${TERM})\`$`).exec(text);
  if (k !== null && k[1] !== undefined && k[2] !== undefined) return { kind: "kept", coll: term(k[1], line), index: term(k[2], line) };
  return refuse(line, "no atom");
}

const CHANGES: readonly Change[] = ["keep", "init", "scalar", "grow", "any"];

/** An effect's entry, `` - `region: change` ``. */
function effect(text: string, line: number): { region: Region; change: Change } {
  const m = /^- `(.+): (\w+)`$/.exec(text);
  if (m === null || m[1] === undefined || m[2] === undefined) return refuse(line, "no effect's entry");
  const change = CHANGES.find((c) => c === m[2]) ?? refuse(line, `${m[2]} is no change`);
  const g = m[1];
  if (g === "st" || g === "vw" || g === "val") return { region: { kind: g }, change };
  const p = new RegExp(`^(${TERM})\\.(\\w+)$`).exec(g);
  if (p === null || p[1] === undefined || p[2] === undefined) return refuse(line, `${g} is no region`);
  const of = term(p[1], line);
  const kind = p[2];
  return { region: kind === "spine" || kind === "cells" || kind === "fields" ? { kind, of } : { kind: "field", of, field: kind }, change };
}

const SORTS: readonly Sort[] = ["Num", "SafeInt", "String", "Array", "TypedArray"];

/** A variable's row of a rule's table. */
function variable(text: string, line: number): RuleVariable {
  const m = /^\| `(\w+)` \| ([^|]+) \| `(\w+)` \|$/.exec(text);
  if (m === null || m[1] === undefined || m[2] === undefined || m[3] === undefined) return refuse(line, "no variable row");
  const roles: { [r: string]: [Role, Normalisation | null] } = {
    "operand": ["operand", null], "index": ["index", null], "written": ["written", null], "result": ["result", null],
    "constant, a shift count": ["constant", "shiftCount"], "constant, read as itself": ["constant", "identity"],
  };
  const role = roles[m[2]];
  if (role === undefined) return refuse(line, `${m[2]} is no role`);
  const sort = SORTS.find((s) => s === m[3]) ?? refuse(line, `${m[3]} is no sort`);
  return { var: base(m[1], line), role: role[0], sort, kind: role[1] };
}

/** The constant's sentence. */
function constant(text: string, line: number): Constant {
  const m = /^The constant: (no lower bound|at least (-?\d+)); (no upper bound|at most (-?\d+)); (read as itself|read as a shift count, modulo 32)\.$/.exec(text);
  if (m === null) return refuse(line, "no constant's sentence");
  return { lower: m[2] === undefined ? null : integer(m[2], line), upper: m[4] === undefined ? null : integer(m[4], line),
    normalisation: m[5] === "read as itself" ? "identity" : "shiftCount" };
}

/** The evidence's sentence: `proved by `p`` or `assumed of `c`, `d``. */
function evidence(text: string, line: number): Evidence {
  const p = /^proved by `([\w.]+)`$/.exec(text);
  if (p !== null && p[1] !== undefined) return { kind: "proved", proof: p[1] };
  const a = /^assumed of (`[^`]+`(?:, `[^`]+`)*)$/.exec(text);
  if (a !== null && a[1] !== undefined) return { kind: "assumed", contracts: a[1].split(", ").map((c) => c.slice(1, -1)) };
  return refuse(line, "no evidence");
}

const DISPLAYS: readonly Display[] = ["arithmetic", "strings", "views"];

/** **The rules' document from the verifier's Markdown**, line by line in the
 * form `RuleExport.rulesMarkdown` writes; any other line is refused. */
export function decodeRules(source: string): RulesDocument {
  const lines = source.split("\n");
  let at = 0;
  const peek = (): string => lines[at] ?? "";
  const next = (): string => lines[at++] ?? refuse(at, "the document ends early");
  const expect = (re: RegExp, what: string): RegExpExecArray => re.exec(next()) ?? refuse(at, `expected ${what}`);
  const blank = (): void => { if (next() !== "") refuse(at, "expected a blank line"); };
  expect(/^# Step rules$/, "the title"); blank();
  const intro = expect(/^The rules of `[\w.]+`, in the paper's order\. A proved rule is sound by `([\w.]+)`, which `([\w.]+)` proves of every proved rule; an assumed rule names the native contracts it rests on\.$/, "the soundness sentence");
  blank();
  expect(/^A fact is `Σ \(coefficient\)·term ≤ bound`, a term a variable or its length `\|variable\|`; `k` is the rule's constant as the rule reads it\.$/, "the facts' sentence");
  const rules: Rule[] = [];
  const list = <T,>(title: string, item: (text: string, line: number) => T): T[] => {
    const head = next();
    if (head === `${title}: none.`) return [];
    if (head !== `${title}:`) refuse(at, `expected ${title}`);
    blank();
    const out: T[] = [];
    while (peek().startsWith("- ")) out.push(item(next(), at));
    return out;
  };
  while (at < lines.length - 1) {
    blank();
    const name = expect(/^## (.+)$/, "a rule's heading")[1] ?? "";
    blank();
    const decl = expect(/^Operation `(\w+)`, in the display `(\w+)`\. Stated by `([\w.]+)`, (.+)\.$/, "the rule's operation and declaration");
    const display = DISPLAYS.find((d) => d === decl[2]) ?? refuse(at, `${decl[2]} is no display`);
    const ev = evidence(decl[4] ?? "", at);
    blank();
    expect(/^\| Variable \| Role \| Sort \|$/, "the variables' table"); expect(/^\| --- \| --- \| --- \|$/, "the table's rule");
    const variables: RuleVariable[] = [];
    while (peek().startsWith("| ")) variables.push(variable(next(), at));
    blank();
    let c: Constant | null = null;
    if (peek().startsWith("The constant:")) { c = constant(next(), at); blank(); }
    const premises = list("Premises", fact);
    blank();
    const conclusion = list("Conclusion", fact);
    blank();
    const atoms = list("Atoms", atom);
    blank();
    const effects = list("Effect", effect);
    rules.push({ name, declaration: decl[3] ?? "", evidence: ev, op: decl[1] ?? "", display, variables, constant: c,
      premises, conclusion, atoms, effect: effects });
  }
  if (lines[at] !== "" || at !== lines.length - 1) refuse(at + 1, "text after the last rule");
  return { statement: intro[1] ?? "", soundness: intro[2] ?? "", rules };
}

/** The verifier's export of the step rules. */
function exportedRules(): RulesDocument {
  const verifier = join(root, "lean/.lake/build/bin/verifier");
  return decodeRules(execFileSync(verifier, ["--export", "rules", "arithmetic"], { encoding: "utf8" }));
}

/* ---- One renderer, three notations ---- */

/** How a notation sets the pieces of a rule. */
type Notation = {
  /** The name of a rule's result. */
  result: string;
  /** The name of the largest safe integer, `2^53 − 1`, and of the largest
   * array length, `2^32 − 1`, where the notation has one. */
  max: string | null;
  maxLength: string | null;
  le: string; lt: string; eq: string; and: string; minus: string; times: string;
  power: (exponent: string) => string;
  /** The second operand of a sort named by a letter: `s'`. */
  prime: (name: string) => string;
  /** An array's name. */
  array: string;
  /** The length of a variable of a sort. */
  length: (sort: Sort, name: string) => string;
  /** The element atom `x[i] ≐ y`, the value converted to the format where `converted`. */
  element: (coll: string, index: string, value: string, converted: boolean) => string;
  /** Every other index of `coll` reads what it read: `Q_{≠i}`. */
  kept: (coll: string, index: string) => string;
  /** An effect: empty, or entries `region: change`. */
  effect: (entries: { region: Region; change: Change }[], name: (t: Term) => string) => string;
  /** The normalised constant's name: a shift count `d` reads `d'`. */
  bound: (c: Constant) => string;
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
  mul: { latex: "\\cdot", markdown: "\\cdot", text: "*" },
};

function operator(op: string, notation: "latex" | "markdown" | "text"): string {
  const symbol = OPERATORS[op];
  if (symbol === undefined) throw new Error(`the rules' document: no symbol for the operator ${op}`);
  return symbol[notation];
}

/** A constant's letter by its kind, `d` for a shift count and `c` otherwise. */
const constantLetter = (c: Constant): string => (c.normalisation === "shiftCount" ? "d" : "c");
const boundName = (c: Constant, prime: string): string => (c.normalisation === "shiftCount" ? `d${prime}` : "c");

/** An effect's region and change in a notation's words. */
function effectEntries(entries: { region: Region; change: Change }[], name: (t: Term) => string,
    word: (w: string) => string, words: { [w: string]: string }): string[] {
  const w = (x: string): string => words[x] ?? word(x);
  return entries.map(({ region, change }) => {
    const g = "of" in region
      ? `${name(region.of)}.${region.kind === "field" ? region.field : word(region.kind)}` : w(region.kind);
    return `${g}:${w(change)}`;
  });
}

const LATEX: Notation = {
  result: "y", max: "M", maxLength: "N", le: "\\le ", lt: "<", eq: "=", and: "\\wedge ", minus: "-", times: "\\,",
  power: (e) => `2^{${e}}`, prime: (n) => `${n}'`, array: "\\mathit{xs}",
  length: (_s, n) => (/^[a-z]$/.test(n) ? `\\len ${n}` : `\\len{${n}}`),
  element: (c, i, v, conv) => `${c}[${i}]\\doteq${conv ? `\\mathit{conv}_t(${v})` : ` ${v}`}`,
  kept: (_c, i) => `Q_{\\ne ${i}}`,
  effect: (entries, name) => entries.length === 0 ? "\\emptyset"
    : `\\{${effectEntries(entries, name, (x) => `\\kw{${x}}`, { st: "\\st", vw: "\\vw", val: "\\val", keep: "\\keep", init: "\\init", grow: "\\grow", any: "\\any" }).join(",")}\\}`,
  bound: (c) => boundName(c, "'"),
};
const MARKDOWN: Notation = {
  result: "r", max: "M", maxLength: null, le: "\\le ", lt: "<", eq: "=", and: ",\\ ", minus: "-", times: "\\,",
  power: (e) => `2^{${e}}`, prime: (n) => `${n}'`, array: "\\mathit{xs}",
  length: (s, n) => (s === "String" ? `\\mathrm{strLength}(${n})` : s === "TypedArray" ? `\\mathrm{view}(${n})` : `|${n}|`),
  element: (c, i, v, conv) => `${c}[${i}]\\doteq${conv ? `\\mathrm{conv}_t(${v})` : ` ${v}`}`,
  kept: (_c, i) => `Q_{\\ne ${i}}`,
  effect: (entries, name) => entries.length === 0 ? "\\emptyset"
    : `\\{${effectEntries(entries, name, (x) => `\\mathsf{${x}}`, { st: "\\mathsf{spines}", vw: "\\mathsf{views}", val: "\\mathsf{values}" }).join(",\\ ")}\\}`,
  bound: (c) => boundName(c, "'"),
};
const TEXT: Notation = {
  result: "y", max: "M", maxLength: "N", le: " ≤ ", lt: " < ", eq: " = ", and: ", ", minus: "−", times: "·",
  power: (e) => `2^{${e}}`, prime: (n) => `${n}′`, array: "xs",
  length: (_s, n) => `|${n}|`,
  element: (c, i, v, conv) => `${c}[${i}] ≐ ${conv ? `conv_t(${v})` : v}`,
  kept: (_c, i) => `Q≠${i}`,
  effect: (entries, name) => entries.length === 0 ? "∅"
    : `{${effectEntries(entries, name, (x) => x, { st: "spines", vw: "views", val: "values" }).join(", ")}}`,
  bound: (c) => boundName(c, "′"),
};

/** A signed summand of a side: its magnitude's text and its sign. */
type Summand = { negative: boolean; text: string };

/** The text of a literal: the largest safe integer and the largest array
 * length by their names where the notation has them, a power of two `2^p`
 * with `p ≥ 8`, or `2^p − 1`. */
function literal(n: number, notation: Notation): string {
  if (n === Number.MAX_SAFE_INTEGER && notation.max !== null) return notation.max;
  if (n === 2 ** 32 - 1 && notation.maxLength !== null) return notation.maxLength;
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

/** A sum of summands; `0` when empty. A negated summand of several parts
 * is parenthesised. */
function sum(parts: Summand[], notation: Notation): string {
  if (parts.length === 0) return "0";
  const text = (p: Summand): string => (p.negative && /[-+−]/.test(p.text.slice(1)) ? `(${p.text})` : p.text);
  return parts.map((p, i) => (i === 0 ? (p.negative ? notation.minus : "") + text(p)
    : `${p.negative ? notation.minus : "+"}${text(p)}`)).join("");
}

/** One side of a fact: a relation's operands. */
type Inequality = { left: string; strict: boolean; right: string };

/** A term `a·t` as a summand, its sign that of its coefficient, flipped where
 * `negate`. */
function termSummand(t: { term: Term; coef: Coef }, name: (t: Term) => string, k: string,
    notation: Notation, negate: boolean): Summand {
  const c = coefSummands(t.coef, k, notation);
  const single = c.length === 1 ? c[0] : undefined;
  const magnitude = single !== undefined ? single.text : `(${sum(c, notation)})`;
  const text = magnitude === "1" ? name(t.term)
    : `${magnitude}${/(^[a-z]|[0-9)])$/.test(magnitude) || notation === TEXT ? notation.times : ""}${name(t.term)}`;
  return { negative: (single !== undefined && single.negative) !== negate, text };
}

const negated = (parts: Summand[]): Summand[] => parts.map((p) => ({ negative: !p.negative, text: p.text }));

const plain = (c: Coef): boolean => c.byConstant === 0 && c.byPower === 0;

/** A fact `Σ aᵢ·tᵢ ≤ b`, set as the paper reads it: a fact with the
 * result's value or length at coefficient ±1 bounds that term by the other
 * terms (`y ≤ E`, `E ≤ y`); a fact with no result's term and the bound
 * `−1` is its positive terms below its negative terms (`P < N`, over the
 * integers); any other with no result's term is its terms in order bounded
 * by `b`, read as `-b ≤ −Σ` where its first term is negative, and `Σ < B`
 * for a bound `B − 1` the notation names or writes as a power of two, `M`
 * excepted; any other fact has its positive terms bounded by its negative
 * terms and the bound. */
function inequality(f: RuleFact, name: (t: Term) => string, k: string, notation: Notation): Inequality {
  const bound = coefSummands(f.bound, k, notation);
  const unit = (c: Coef): number => (plain(c) && Math.abs(c.lit) === 1 ? c.lit : 0);
  const result = f.terms.find((t) => t.term.var === "result" && unit(t.coef) !== 0);
  if (result !== undefined) {
    const others = f.terms.filter((t) => t !== result);
    const subject = name(result.term);
    return unit(result.coef) > 0
      ? { left: subject, strict: false, right: sum([...others.map((t) => termSummand(t, name, k, notation, true)), ...bound], notation) }
      : { left: sum([...others.map((t) => termSummand(t, name, k, notation, false)), ...negated(bound)], notation), strict: false, right: subject };
  }
  const positive: Summand[] = [];
  const negative: Summand[] = [];
  for (const t of f.terms) {
    const s = termSummand(t, name, k, notation, false);
    (s.negative ? negative : positive).push({ negative: false, text: s.text });
  }
  if (!f.terms.some((t) => t.term.var === "result")) {
    if (plain(f.bound) && f.bound.lit === -1 && positive.length > 0 && negative.length > 0) {
      return { left: sum(positive, notation), strict: true, right: sum(negative, notation) };
    }
    const first = f.terms[0];
    const flip = first !== undefined && termSummand(first, name, k, notation, false).negative;
    const expr = sum(f.terms.map((t) => termSummand(t, name, k, notation, flip)), notation);
    if (flip) return { left: sum(negated(bound), notation), strict: false, right: expr };
    const only = bound.length === 1 ? bound[0] : undefined;
    const strict = only !== undefined && !only.negative && plain(f.bound) &&
      f.bound.lit !== Number.MAX_SAFE_INTEGER && literal(f.bound.lit + 1, notation) !== String(f.bound.lit + 1);
    return { left: expr, strict, right: strict ? literal(f.bound.lit + 1, notation) : sum(bound, notation) };
  }
  return { left: sum(positive, notation), strict: false, right: sum([...negative, ...bound], notation) };
}

/** Facts set as a conjunction: an equality where two facts bound each
 * other, and a chain `A ≤ X ≤ B` where one fact's right side is the next
 * one's left and no other fact bounds `X` from below. */
function conjunction(facts: RuleFact[], name: (t: Term) => string, k: string, notation: Notation): string[] {
  const parts = facts.map((f) => inequality(f, name, k, notation));
  const out: string[] = [];
  const below = (side: string, i: number): boolean => parts.some((p, j) => j !== i && p.right === side);
  for (let i = 0; i < parts.length; i++) {
    const a = parts[i];
    if (a === undefined) continue;
    const b = parts[i + 1];
    const rel = (x: Inequality): string => (x.strict ? notation.lt : notation.le);
    if (b !== undefined && !a.strict && !b.strict && a.left === b.right && a.right === b.left) {
      out.push(`${a.left}${notation.eq}${a.right}`);
      i++;
    } else if (b !== undefined && a.right === b.left && !below(a.right, i)) {
      out.push(`${a.left}${rel(a)}${a.right}${rel(b)}${b.right}`);
      i++;
    } else out.push(`${a.left}${rel(a)}${a.right}`);
  }
  return out;
}

const constantOf = (r: Rule): Constant | undefined => r.constant ?? undefined;

/** A rule's variable, as the export states it. */
function variableOf(r: Rule, x: Base): RuleVariable {
  const v = r.variables.find((w) => w.var === x);
  if (v === undefined) throw new Error(`the rules' document: rule ${r.name} states no variable ${x}`);
  return v;
}

/** The letter of a variable by its role and sort, one convention for every
 * rule: an operand of `SafeInt` is `a` as the first operand and `b` as the
 * second, an operand of `Num` is `x`, a `String` `s` and `s'`, a
 * `TypedArray` `b`, an `Array` `xs`, an index `i`, a written value `v`, a
 * constant `d` as a shift count and `c` otherwise, and the result the
 * notation's. */
function letter(v: RuleVariable, notation: Notation): string {
  switch (v.role) {
    case "result": return notation.result;
    case "constant": return v.kind === "shiftCount" ? "d" : "c";
    case "index": return "i";
    case "written": return "v";
    case "operand":
      switch (v.sort) {
        case "Num": return "x";
        case "SafeInt": return v.var === "left" ? "a" : "b";
        case "String": return v.var === "left" ? "s" : notation.prime("s");
        case "TypedArray": return "b";
        case "Array": return notation.array;
      }
  }
}

/** The slot of a rule's right operand: its letter as an operand of its sort. */
function slotOf(r: Rule): string {
  const v = variableOf(r, "right");
  return v.role === "constant" ? (v.sort === "Num" ? "x" : "b") : letter(v, MARKDOWN);
}

/** The names of a rule's terms: a variable's letter, a length the
 * notation's length of the variable's sort. */
function names(r: Rule, notation: Notation): (t: Term) => string {
  return (t) => {
    const v = variableOf(r, t.var);
    const n = letter(v, notation);
    return t.len ? notation.length(v.sort, n) : n;
  };
}

/** The sorts of a rule's operands and constant, as the export states them;
 * those of one sort grouped, in the order of the variables. */
function sorts(r: Rule, sort: (s: Sort) => string, of: string, sep: string, notation: Notation): string {
  const groups: { names: string[]; sort: Sort }[] = [];
  for (const v of r.variables.filter((w) => w.role !== "result")) {
    const last = groups[groups.length - 1];
    const name = letter(v, notation);
    if (last !== undefined && last.sort === v.sort) last.names.push(name);
    else groups.push({ names: [name], sort: v.sort });
  }
  return groups.map((g) => `${g.names.join(",")}${of}${sort(g.sort)}`).join(sep);
}

/** The facts `int(v)` of a rule's variables of `SafeInt` with one of the roles. */
function ints(r: Rule, roles: Role[], name: (v: RuleVariable) => string, int: (n: string) => string): string[] {
  return r.variables.filter((v) => roles.includes(v.role) && v.sort === "SafeInt").map((v) => int(name(v)));
}

/** A rule's conclusion: its facts, then its atoms. */
function postcondition(r: Rule, name: (t: Term) => string, k: string, notation: Notation): string[] {
  return [...conjunction(r.conclusion, name, k, notation),
    ...r.atoms.map((a) => a.kind === "elem" ? notation.element(name(a.coll), name(a.index), name(a.value), a.converted)
      : notation.kept(name(a.coll), name(a.index)))];
}

/** A step in source form, `y = s.length`, `y = b[i]`, `b[i] = v`, `y = s + s'`. */
function sourceStep(r: Rule, name: (t: Term) => string, result: string): string {
  const l = name({ var: "left", len: false });
  const at = (): string => `${l}[${name({ var: "right", len: false })}]`;
  switch (r.op) {
    case "strLength": case "viewLength": return `${result} = ${l}.length`;
    case "strRead": case "viewRead": return `${result} = ${at()}`;
    case "viewWrite": return `${at()} = ${name({ var: "third", len: false })}`;
    default: return `${result} = ${l} ${operator(r.op, "text")} ${name({ var: "right", len: false })}`;
  }
}

/** The step of a rule in the paper: a binary operator of the arithmetic
 * display in mathematics, `y=a+b`, any other in code. */
function paperStep(r: Rule, name: (t: Term) => string): string {
  if (r.display === "arithmetic") {
    const symbol = operator(r.op, "latex");
    return `y=${name({ var: "left", len: false })}${symbol}${/[A-Za-z]$/.test(symbol) ? " " : ""}${name({ var: "right", len: false })}`;
  }
  return `\\code{${sourceStep(r, name, "y").replace(/&/g, "\\&")}}`;
}

/** Whether a display's rows carry an effect column; a display without one
 * holds rules of the empty effect alone, which its text states. */
const effectColumn = (d: Display): boolean => d === "views";

function checkEffect(r: Rule): void {
  if (!effectColumn(r.display) && r.effect.length > 0) {
    throw new Error(`the rules' document: rule ${r.name} has an effect, which the display ${r.display} does not show`);
  }
}

/** The rule's triple in the paper's notation, `{P} y = x op c {Q}`. */
function paperTriple(r: Rule): string {
  const c = constantOf(r);
  const k = c === undefined ? "" : LATEX.bound(c);
  const n = names(r, LATEX);
  const pre = conjunction(r.premises, n, k, LATEX);
  const post = postcondition(r, n, k, LATEX);
  const set = (xs: string[]): string => (xs.length === 0 ? "\\kw{true}" : xs.join(LATEX.and));
  return `\\hoare{${set(pre)}}{${paperStep(r, n)}}{${set(post)}}`;
}

/** The rules of a display, in the export's order. */
const ofDisplay = (doc: RulesDocument, d: Display): Rule[] => doc.rules.filter((r) => r.display === d);

/** The paper's rule rows of a display: one row per triple, its operands'
 * sorts, then the triple; the rule's name on its first triple's row. Where
 * the display has an effect column, the sorts take a row of their own,
 * above the triple and its effect, so that the row fits the page. */
export function paperRows(doc: RulesDocument, display: Display): string {
  const rules = ofDisplay(doc, display);
  return rules.map((r, i) => {
    checkEffect(r);
    const name = i > 0 && rules[i - 1]?.name === r.name ? "" : `\\textsc{${r.name}}`;
    const sorted = sorts(r, (s) => `\\mathit{${s}}`, ":", ",\\ ", LATEX);
    return effectColumn(display)
      ? `${name} & ${sorted} & \\\\\n & ${paperTriple(r)} & :${LATEX.effect(r.effect, names(r, LATEX))}`
      : `${name} & ${sorted} & ${paperTriple(r)}`;
  }).join("\\\\[3pt]\n") + "\n";
}

/** A constant's side condition and normalisation, as premises. */
function constantPremises(c: Constant, notation: Notation): string[] {
  const bounds = [c.lower === null ? "" : `${literal(c.lower, notation)}${notation.le}`, constantLetter(c),
    c.upper === null ? "" : `${notation.lt}${literal(c.upper + 1, notation)}`].join("");
  const side = c.lower === null && c.upper === null ? [] : [bounds];
  return c.normalisation === "shiftCount" ? [...side, `${boundName(c, notation === TEXT ? "′" : "'")}${notation.eq}${constantLetter(c)}${notation === TEXT ? " mod " : "\\bmod "}32`] : side;
}

/** The step of a rule in the notation of the implementation's documents:
 * `r ← a op b` for a binary operator of the arithmetic display, the source
 * form otherwise. */
function markdownStep(r: Rule, name: (t: Term) => string): string {
  if (r.display === "arithmetic") {
    const symbol = operator(r.op, "markdown");
    return `r\\leftarrow ${name({ var: "left", len: false })}${symbol}${/[A-Za-z]$/.test(symbol) ? " " : ""}${slotOf(r)}`;
  }
  const l = name({ var: "left", len: false });
  const at = (): string => `${l}[${name({ var: "right", len: false })}]`;
  switch (r.op) {
    case "strLength": case "viewLength": return `r\\leftarrow ${l}.\\mathtt{length}`;
    case "strRead": case "viewRead": return `r\\leftarrow ${at()}`;
    case "viewWrite": return `${at()}\\leftarrow ${name({ var: "third", len: false })}`;
    default: return `r\\leftarrow ${l}${operator(r.op, "markdown")}${name({ var: "right", len: false })}`;
  }
}

/** A rule as an inference in the notation of the implementation's
 * documents: `int(a)`, `K ⊢ b = d`, the premises, over
 * `K ⊢ r ← a op b ⊣ int(r), …`, then the name, the sorts and, where the
 * display has one, the effect. */
function markdownRule(r: Rule): string {
  checkEffect(r);
  const c = constantOf(r);
  const k = c === undefined ? "" : MARKDOWN.bound(c);
  const n = names(r, MARKDOWN);
  const above = [
    ...ints(r, ["operand", "index"], (v) => (v.var === "right" ? slotOf(r) : letter(v, MARKDOWN)), (x) => `\\mathrm{int}(${x})`),
    ...(r.constant === null ? []
      : [`K\\vdash ${slotOf(r)}=${n({ var: "right", len: false })}`, ...constantPremises(r.constant, MARKDOWN)]),
    ...conjunction(r.premises, n, k, MARKDOWN).map((p) => `K\\vdash ${p}`),
  ];
  const below = [...ints(r, ["result"], (v) => letter(v, MARKDOWN), (x) => `\\mathrm{int}(${x})`), ...postcondition(r, n, k, MARKDOWN)];
  const sorted = sorts(r, (s) => `\\mathit{${s}}`, ":", ",\\ ", MARKDOWN);
  const effect = effectColumn(r.display) ? `\\quad :${MARKDOWN.effect(r.effect, n)}` : "";
  return `\\frac{${above.join("\\quad ")}}\n     {K\\vdash ${markdownStep(r, n)}${below.length === 0 ? "" : `\\dashv ${below.join(",\\ ")}`}}\n     \\ \\textsf{${r.name}}\\quad ${sorted}${effect}`;
}

/** The evidence in words: `proved by p`, `assumed of c, d`. */
const evidenceWords = (e: Evidence): string => (e.kind === "proved" ? `proved by ${e.proof}` : `assumed of ${e.contracts.join(", ")}`);

/** A display's rules in the implementation's documents: each a comment
 * naming the rule's declaration and evidence, then its `math` block. */
export function markdownRules(doc: RulesDocument, display: Display): string {
  return ofDisplay(doc, display).map((r) => `<!-- ${r.declaration}, ${evidenceWords(r.evidence)} -->\n\n\`\`\`math\n${markdownRule(r)}\n\`\`\`\n`).join("\n");
}

/** A rule in the record notation dev/record-render.mts draws: premises,
 * a bar with the rule's name, the conclusion. */
function textRule(r: Rule): string[] {
  const c = constantOf(r);
  const k = c === undefined ? "" : TEXT.bound(c);
  const n = names(r, TEXT);
  const above = [
    sorts(r, (s) => s, " : ", ", ", TEXT),
    ...ints(r, ["operand", "index"], (v) => letter(v, TEXT), (x) => `int(${x})`),
    ...(r.constant === null ? [] : constantPremises(r.constant, TEXT)),
    ...conjunction(r.premises, n, k, TEXT),
  ];
  const below = [...ints(r, ["result"], (v) => letter(v, TEXT), (x) => `int(${x})`), ...postcondition(r, n, k, TEXT)];
  const step = `\`${sourceStep(r, n, "y")}\``;
  const effect = effectColumn(r.display) ? `   : ${TEXT.effect(r.effect, n)}` : "";
  return [above.length === 0 ? "true" : above.join("   "), `──────── (${r.name})`,
    `${step}${below.length === 0 ? "" : ` ⊣ ${below.join(", ")}`}${effect}`];
}

const esc = (s: string): string => s.replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;");

/** The rules' page: each rule drawn as a record's rule, with its declaration and evidence. */
export function rulesPage(doc: RulesDocument): string {
  const cards = doc.rules.map((r) => {
    const ev = r.evidence.kind === "proved" ? `<dt>Proof</dt><dd><code>${esc(r.evidence.proof)}</code></dd>`
      : `<dt>Assumed of</dt><dd>${r.evidence.contracts.map((c) => `<code>${esc(c)}</code>`).join(", ")}</dd>`;
    return `<section class="card"><h3>${esc(r.name)}</h3>${ruleBlocks(textRule(r))}
<dl class="facts"><dt>Rule</dt><dd><code>${esc(r.declaration)}</code></dd>${ev}</dl></section>`;
  });
  return `<!doctype html>
<html><head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">
<title>Step Rules</title>
${Object.values(FACES).map((f) => `<link rel="stylesheet" href="${f.href}">`).join("")}
<style>${CSS}</style></head><body><main><header><h1>Step Rules</h1>
<p class="lede">The rules of <code>ArithmeticRules.rules</code>: a proved rule sound by <code>${esc(doc.soundness)}</code> (the statement <code>${esc(doc.statement)}</code>), an assumed rule with the native contracts it rests on.</p></header>
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
    produce: (): string => paperRows(arithmeticRules(), "arithmetic") },
  { id: "paper-string-rules", destination: "docs/drafts/tolerant-frames-note/note.tex", format: "latex",
    produce: (): string => paperRows(arithmeticRules(), "strings") },
  { id: "paper-view-rules", destination: "docs/drafts/tolerant-frames-note/note.tex", format: "latex",
    produce: (): string => paperRows(arithmeticRules(), "views") },
  { id: "arithmetic-rules", destination: "docs/ARITHMETIC.md", format: "markdown",
    produce: (): string => markdownRules(arithmeticRules(), "arithmetic") },
  { id: "string-rules", destination: "docs/ARITHMETIC.md", format: "markdown",
    produce: (): string => markdownRules(arithmeticRules(), "strings") },
  { id: "view-rules", destination: "docs/SOURCE-CONTRACTS.md", format: "markdown",
    produce: (): string => markdownRules(arithmeticRules(), "views") },
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
