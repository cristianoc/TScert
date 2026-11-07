// The written preconditions of a function declaration (RFC #115, the draft
// docs/drafts/checked-bound-annotations.md; PROGRAM-TYPING.md, "Written
// preconditions"): a `@requires C` tag of the declaration's leading JSDoc
// comment, read from the source text, its clause parsed here and elaborated
// to index facts at the call's positions (`HeapKnowledge.IndexFact`: 0 the
// receiver, i + 1 the i-th actual).
//
// The clause language read here is a conjunction of atoms over the
// declaration's parameters:
//
//   C ::= A && C | A
//   A ::= safeInteger(x)
//       | E rel E           rel ∈ { <, <=, >, >=, === }, every parameter E
//                           names stated a safe integer by the clause
//       | k < xs.length | k <= xs.length | xs.length > k | xs.length >= k
//                           k stated a safe integer and 0 <= k by the clause,
//                           xs an array parameter
//   E ::= n | x | n * x | E + E | E - E | -E
//
// with n an integer literal and x a parameter. Each atom's meaning is the
// index fact it elaborates to: `safeInteger(x)` is `int(x)`; a comparison of
// linear expressions is a linear fact over the integers the parameters hold,
// which for safe integers is the comparison's IEEE answer; `k < xs.length`
// is `bound(xs, k, strict)`, k an index below (at most) the length of the
// store `xs` holds, which is the array's `length`. Every other form of the
// draft's grammar (guards, `old`, `result`, paths other than an array
// parameter's length, `||`, `!`) is refused with the clause's location.
import type { IndexFact, LinearFact } from "./declaration-types.mts";

/** A parameter a clause may name: its name, its call position, whether its
 * type is an array, whose length is its store's. */
export type ClauseParameter = { name: string; position: number; array: boolean };

/** The text of each `@requires` tag of the last JSDoc comment (`/** … *\/`)
 * in a declaration's leading trivia, with each line's leading `*` removed. */
export function requiresTags(trivia: string): string[] {
  const open = trivia.lastIndexOf("/**");
  if (open < 0) return [];
  const close = trivia.indexOf("*/", open + 3);
  if (close < 0) return [];
  const lines = trivia.slice(open + 3, close).split("\n").map(l => l.replace(/^\s*\*?\s?/, ""));
  const tags: string[] = [];
  let current: string[] | null = null;
  for (const line of lines) {
    const tag = /^@(\w+)\b(.*)$/.exec(line.trim());
    if (tag) {
      if (current) tags.push(current.join(" "));
      current = tag[1] === "requires" ? [tag[2] ?? ""] : null;
    } else if (current) current.push(line);
  }
  if (current) tags.push(current.join(" "));
  return tags.map(t => t.trim());
}

type Token = { k: "num"; v: number } | { k: "name"; v: string } | { k: "op"; v: string };

function tokens(text: string): Token[] | string {
  const out: Token[] = [];
  let i = 0;
  while (i < text.length) {
    const c = text[i] ?? "";
    if (/\s/.test(c)) { i++; continue; }
    const num = /^\d+/.exec(text.slice(i));
    if (num) {
      const v = Number(num[0]);
      if (!Number.isSafeInteger(v)) return `the literal ${num[0]} is no safe integer`;
      out.push({ k: "num", v }); i += num[0].length; continue;
    }
    const name = /^[A-Za-z_$][\w$]*/.exec(text.slice(i));
    if (name) { out.push({ k: "name", v: name[0] }); i += name[0].length; continue; }
    const op = /^(===|!==|<=|>=|&&|\|\||[!<>+\-*().,])/.exec(text.slice(i));
    if (op) { out.push({ k: "op", v: op[0] }); i += op[0].length; continue; }
    return `the clause has a character outside its language: ${c}`;
  }
  return out;
}

/** A linear expression: coefficients by parameter name and a constant. */
type Linear = { terms: Map<string, number>; constant: number };
/** A term of an atom: a linear expression, or the length of a parameter. */
type Term = { k: "linear"; e: Linear } | { k: "length"; of: string };
type Atom = { k: "safeInteger"; of: string } | { k: "compare"; op: string; left: Term; right: Term };

class Parser {
  private at = 0;
  private readonly ts: Token[];
  constructor(ts: Token[]) { this.ts = ts; }
  private peek(): Token | undefined { return this.ts[this.at]; }
  private take(): Token | undefined { return this.ts[this.at++]; }
  private isOp(v: string): boolean { const t = this.peek(); return t !== undefined && t.k === "op" && t.v === v; }
  private expect(v: string): void {
    if (!this.isOp(v)) throw new ClauseError(`the clause expects ${v}`);
    this.at++;
  }
  done(): boolean { return this.at === this.ts.length; }
  conjunction(): Atom[] {
    const atoms = [this.atom()];
    while (this.isOp("&&")) { this.at++; atoms.push(this.atom()); }
    if (!this.done()) throw new ClauseError("the clause is a conjunction of atoms (`&&`), no other connective");
    return atoms;
  }
  private atom(): Atom {
    const t = this.peek();
    if (t && t.k === "name" && t.v === "safeInteger") {
      this.at++;
      this.expect("(");
      const x = this.take();
      if (!x || x.k !== "name") throw new ClauseError("`safeInteger` takes a parameter");
      this.expect(")");
      return { k: "safeInteger", of: x.v };
    }
    const left = this.term();
    const op = this.take();
    if (!op || op.k !== "op" || !["<", "<=", ">", ">=", "==="].includes(op.v))
      throw new ClauseError("an atom compares two terms with <, <=, >, >= or ===");
    const right = this.term();
    return { k: "compare", op: op.v, left, right };
  }
  private term(): Term {
    const t = this.peek();
    const next = this.ts[this.at + 1];
    const after = this.ts[this.at + 2];
    if (t && t.k === "name" && next && next.k === "op" && next.v === "." ) {
      if (!after || after.k !== "name" || after.v !== "length")
        throw new ClauseError("a path is a parameter's `length`, no other");
      this.at += 3;
      return { k: "length", of: t.v };
    }
    return { k: "linear", e: this.sum() };
  }
  private sum(): Linear {
    let e = this.product();
    while (this.isOp("+") || this.isOp("-")) {
      const sign = this.isOp("+") ? 1 : -1;
      this.at++;
      e = add(e, this.product(), sign);
    }
    return e;
  }
  private product(): Linear {
    if (this.isOp("-")) { this.at++; return scale(this.product(), -1); }
    if (this.isOp("(")) { this.at++; const e = this.sum(); this.expect(")"); return e; }
    const t = this.take();
    if (!t) throw new ClauseError("the clause ends inside a term");
    if (t.k === "num") {
      if (this.isOp("*")) {
        this.at++;
        const x = this.take();
        if (!x || x.k !== "name") throw new ClauseError("a product is an integer literal times a parameter");
        return { terms: new Map([[x.v, t.v]]), constant: 0 };
      }
      return { terms: new Map(), constant: t.v };
    }
    if (t.k === "name") return { terms: new Map([[t.v, 1]]), constant: 0 };
    throw new ClauseError(`the clause has ${t.v} where a term is expected`);
  }
}

class ClauseError extends Error {}

function add(a: Linear, b: Linear, sign: number): Linear {
  const terms = new Map(a.terms);
  for (const [x, c] of b.terms) terms.set(x, (terms.get(x) ?? 0) + sign * c);
  return { terms, constant: a.constant + sign * b.constant };
}
function scale(a: Linear, k: number): Linear {
  return { terms: new Map([...a.terms].map(([x, c]): [string, number] => [x, k * c])), constant: k * a.constant };
}

/** The positions an index fact names. */
export function indexFactPositions(f: IndexFact): number[] {
  if ("index" in f) return [f.index.slot];
  if ("int" in f) return [f.int.slot];
  if ("length" in f) return [f.length.array, f.length.length];
  if ("bound" in f) return [f.bound.array, f.bound.index];
  const F = f.linear.fact;
  return ("le" in F ? F.le.form : F.ne.form).map(([x]) => x);
}

/** The index facts a declaration's `@requires` clauses elaborate to, or the
 * reason one is refused. */
export function elaborateRequires(clauses: readonly string[], params: readonly ClauseParameter[]):
    { facts: IndexFact[] } | { refused: string } {
  try {
    const atoms = clauses.flatMap(text => {
      const ts = tokens(text);
      if (typeof ts === "string") throw new ClauseError(ts);
      return new Parser(ts).conjunction();
    });
    const param = (name: string): ClauseParameter => {
      const p = params.find(q => q.name === name);
      if (!p) throw new ClauseError(`the clause names ${name}, which is no parameter of the declaration`);
      return p;
    };
    const ints = new Set(atoms.flatMap(a => a.k === "safeInteger" ? [param(a.of).name] : []));
    const facts: IndexFact[] = [];
    const linearFacts: { form: Map<string, number>; bound: number }[] = [];
    const lessEq = (l: Linear, r: Linear, strict: boolean): void => {
      const d = add(l, r, -1);
      const form = new Map([...d.terms].filter(([, c]) => c !== 0));
      for (const x of form.keys())
        if (!ints.has(param(x).name)) throw new ClauseError(`the comparison names ${x}, which the clause does not state a safe integer`);
      linearFacts.push({ form, bound: -d.constant - (strict ? 1 : 0) });
    };
    const lengths: { array: string; index: string; strict: boolean }[] = [];
    for (const a of atoms) {
      if (a.k === "safeInteger") { facts.push({ int: { slot: param(a.of).position } }); continue; }
      const { op, left, right } = a;
      if (left.k === "length" || right.k === "length") {
        // `k < xs.length` and its mirrored and inclusive forms.
        const [index, length, strict] =
          left.k === "linear" && right.k === "length" && (op === "<" || op === "<=") ? [left.e, right.of, op === "<"]
          : left.k === "length" && right.k === "linear" && (op === ">" || op === ">=") ? [right.e, left.of, op === ">"]
          : (() => { throw new ClauseError("a length is compared as `k < xs.length` or `k <= xs.length`, no other way"); })();
        const k = [...index.terms];
        if (index.constant !== 0 || k.length !== 1 || k[0]?.[1] !== 1)
          throw new ClauseError("a length bounds a parameter, no other term");
        const name = k[0]?.[0] ?? "";
        if (!param(length).array) throw new ClauseError(`${length} is no array parameter`);
        if (!ints.has(param(name).name)) throw new ClauseError(`the index ${name} is not stated a safe integer`);
        lengths.push({ array: length, index: name, strict });
        continue;
      }
      if (left.k !== "linear" || right.k !== "linear") throw new ClauseError("a comparison of linear terms");
      if (op === "<") lessEq(left.e, right.e, true);
      else if (op === "<=") lessEq(left.e, right.e, false);
      else if (op === ">") lessEq(right.e, left.e, true);
      else if (op === ">=") lessEq(right.e, left.e, false);
      else { lessEq(left.e, right.e, false); lessEq(right.e, left.e, false); }
    }
    for (const l of lengths) {
      const nonnegative = linearFacts.some(f => f.form.size === 1 && f.form.get(l.index) === -1 && f.bound <= 0);
      if (!nonnegative) throw new ClauseError(`the index ${l.index} is bounded by a length but not stated 0 <= ${l.index}`);
      facts.push({ bound: { array: param(l.array).position, index: param(l.index).position, strict: l.strict } });
    }
    for (const f of linearFacts) {
      const form: [number, number][] = [...f.form].map(([x, c]): [number, number] => [param(x).position, c])
        .sort((a, b) => a[0] - b[0]);
      const fact: LinearFact = { le: { form, bound: f.bound } };
      facts.push({ linear: { fact } });
    }
    return { facts };
  } catch (e) {
    if (e instanceof ClauseError) return { refused: e.message };
    throw e;
  }
}
