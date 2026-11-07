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
//   A ::= safeInteger(x) | E rel E      rel ∈ { <, <=, >, >=, === }
//   E ::= n | x | xs.length | n * x | n * xs.length | E + E | E - E | -E | (E)
//
// with n an integer literal, x a parameter the clause states a safe integer
// and xs an array or typed array parameter. Each atom's meaning is the index
// facts it elaborates to: `safeInteger(x)` is `int(x)`; a comparison is the
// linear fact over the integers its terms denote, a parameter's value, its
// array's length or its typed array's element count (`HeapKnowledge.Term`),
// with every sum, difference and
// product it computes stated a safe integer. Where those facts hold, each
// side of the comparison evaluates under JavaScript's arithmetic to that
// safe integer exactly, so the comparison's answer is the fact's. Every other
// form of the draft's grammar (guards, `old`, `result`, paths other than an
// array or typed array parameter's length, `||`, `!`) is refused with the
// clause's location.
import type { IndexFact, LinearFact, LinearTerm } from "./declaration-types.mts";

/** A parameter a clause may name: its name, its call position, and what its
 * `length` is: an array's, its store's length (`length`); a typed array's,
 * its element count (`view`); or none a clause names (`null`). */
export type ClauseParameter = { name: string; position: number; length: "length" | "view" | null };

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

/** A linear expression: coefficients by term and a constant, a term a
 * parameter's name or `xs.length`, and the subexpressions JavaScript computes
 * on the way (`steps`), each a sum, difference or product. */
type Linear = { terms: Map<string, number>; constant: number; steps: Linear[] };
type Atom = { k: "safeInteger"; of: string } | { k: "compare"; op: string; left: Linear; right: Linear };

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
    const left = this.sum();
    const op = this.take();
    if (!op || op.k !== "op" || !["<", "<=", ">", ">=", "==="].includes(op.v))
      throw new ClauseError("an atom compares two terms with <, <=, >, >= or ===");
    const right = this.sum();
    return { k: "compare", op: op.v, left, right };
  }
  private sum(): Linear {
    let e = this.product();
    while (this.isOp("+") || this.isOp("-")) {
      const sign = this.isOp("+") ? 1 : -1;
      this.at++;
      e = computed(add(e, this.product(), sign));
    }
    return e;
  }
  /** A parameter or its array's `length`. */
  private variable(): string {
    const x = this.take();
    if (!x || x.k !== "name") throw new ClauseError("a product is an integer literal times a parameter or a length");
    if (this.isOp(".")) {
      this.at++;
      const f = this.take();
      if (!f || f.k !== "name" || f.v !== "length") throw new ClauseError("a path is a parameter's `length`, no other");
      return `${x.v}.length`;
    }
    return x.v;
  }
  private product(): Linear {
    if (this.isOp("-")) { this.at++; return scale(this.product(), -1); }
    if (this.isOp("(")) { this.at++; const e = this.sum(); this.expect(")"); return e; }
    const t = this.peek();
    if (!t) throw new ClauseError("the clause ends inside a term");
    if (t.k === "num") {
      this.at++;
      if (this.isOp("*")) {
        this.at++;
        return computed({ terms: new Map([[this.variable(), t.v]]), constant: 0, steps: [] });
      }
      return { terms: new Map(), constant: t.v, steps: [] };
    }
    if (t.k === "name") return { terms: new Map([[this.variable(), 1]]), constant: 0, steps: [] };
    throw new ClauseError(`the clause has ${t.v} where a term is expected`);
  }
}

class ClauseError extends Error {}

function add(a: Linear, b: Linear, sign: number): Linear {
  const terms = new Map(a.terms);
  for (const [x, c] of b.terms) terms.set(x, (terms.get(x) ?? 0) + sign * c);
  return { terms, constant: a.constant + sign * b.constant, steps: [...a.steps, ...b.steps] };
}
/** `-e`, which JavaScript computes exactly. */
function scale(a: Linear, k: number): Linear {
  return { terms: new Map([...a.terms].map(([x, c]): [string, number] => [x, k * c])), constant: k * a.constant,
    steps: a.steps };
}
/** A subexpression JavaScript computes, recorded among its steps. */
function computed(e: Linear): Linear {
  return { ...e, steps: [...e.steps, { terms: e.terms, constant: e.constant, steps: [] }] };
}

/** The position a linear term reads. */
export function termSlot(t: LinearTerm): number {
  return "value" in t ? t.value.slot : "length" in t ? t.length.slot : t.view.slot;
}

/** The positions an index fact names. */
export function indexFactPositions(f: IndexFact): number[] {
  if ("index" in f) return [f.index.slot];
  if ("int" in f) return [f.int.slot];
  if ("length" in f) return [f.length.array, f.length.length];
  if ("bound" in f) return [f.bound.array, f.bound.index];
  const F = f.linear.fact;
  return ("le" in F ? F.le.form : F.ne.form).map(([t]) => termSlot(t));
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
    const term = (key: string): LinearTerm => {
      if (key.endsWith(".length")) {
        const p = param(key.slice(0, -".length".length));
        if (p.length === null)
          throw new ClauseError(`${p.name} is no array or typed array parameter, whose length a clause names`);
        return p.length === "length" ? { length: { slot: p.position } } : { view: { slot: p.position } };
      }
      const p = param(key);
      if (!ints.has(p.name)) throw new ClauseError(`the comparison names ${key}, which the clause does not state a safe integer`);
      return { value: { slot: p.position } };
    };
    const facts: IndexFact[] = atoms.flatMap(a => a.k === "safeInteger" ? [{ int: { slot: param(a.of).position } }] : []);
    const seen = new Set<string>();
    /** The fact `Σ c·t ≤ bound`, each term once, sorted by position and kind. */
    const lessEq = (terms: Map<string, number>, bound: number): void => {
      if (!Number.isSafeInteger(bound)) throw new ClauseError("the clause's constants lie outside the safe integers");
      const form: [LinearTerm, number][] = [...terms].filter(([, c]) => c !== 0)
        .map(([x, c]): [LinearTerm, number] => [term(x), c])
        .sort((a, b) => code(a[0]) - code(b[0]));
      const fact: LinearFact = { le: { form, bound } };
      const key = JSON.stringify(fact);
      if (!seen.has(key)) { seen.add(key); facts.push({ linear: { fact } }); }
    };
    const compare = (l: Linear, r: Linear, strict: boolean): void => {
      const d = add(l, r, -1);
      lessEq(d.terms, -d.constant - (strict ? 1 : 0));
    };
    for (const a of atoms) {
      if (a.k === "safeInteger") continue;
      const { op, left, right } = a;
      // Each computed subexpression a safe integer, −(2^53 − 1) ≤ e ≤ 2^53 − 1,
      // stated of its terms `t` as −(2^53 − 1) − c ≤ t ≤ 2^53 − 1 − c, each
      // bound at most 2^53 − 1: stronger where c's sign would raise it. A
      // range of one term with coefficient ±1 at 2^53 − 1 is what the term's
      // own range states, and is left out.
      for (const e of [...left.steps, ...right.steps]) {
        const range = (terms: Map<string, number>, bound: number): void => {
          const nonzero = [...terms].filter(([, c]) => c !== 0);
          const own = nonzero.length === 1 && Math.abs(nonzero[0]?.[1] ?? 0) === 1 && bound >= MAX_SAFE;
          if (!own) lessEq(terms, Math.min(bound, MAX_SAFE));
        };
        range(e.terms, MAX_SAFE - e.constant);
        range(scale(e, -1).terms, MAX_SAFE + e.constant);
      }
      if (op === "<") compare(left, right, true);
      else if (op === "<=") compare(left, right, false);
      else if (op === ">") compare(right, left, true);
      else if (op === ">=") compare(right, left, false);
      else { compare(left, right, false); compare(right, left, false); }
    }
    return { facts };
  } catch (e) {
    if (e instanceof ClauseError) return { refused: e.message };
    throw e;
  }
}

const MAX_SAFE = Number.MAX_SAFE_INTEGER;

/** A term's place in a normal form (`HeapKnowledge.Term.code`): a position's
 * value, then its length, then its element count. */
function code(t: LinearTerm): number {
  return "value" in t ? 3 * t.value.slot : "length" in t ? 3 * t.length.slot + 1 : 3 * t.view.slot + 2;
}
