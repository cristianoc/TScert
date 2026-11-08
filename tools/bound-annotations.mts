// The preconditions of a function declaration (RFC #115, the draft
// docs/drafts/checked-bound-annotations.md; PROGRAM-TYPING.md, 
// "Preconditions"): a `@requires C` tag of the declaration's leading JSDoc
// comment, read from the source text, its clause parsed here and elaborated
// to index facts at the call's positions (`HeapKnowledge.IndexFact`: 0 the
// receiver, i + 1 the i-th actual).
//
// The clause language read here is a conjunction of atoms over the
// declaration's parameters, after guards:
//
//   K ::= G || K | C        G ::= p === null | p === undefined
//   C ::= A && C | A | forall i in p: B
//   A ::= safeInteger(p) | E rel E      rel ∈ { <, <=, >, >=, === }
//   E ::= n | p | p.length | n * p | n * p.length | E + E | E - E | -E | (E)
//   p ::= x | p.f
//   B ::= A' && B | A'      A' an atom over E, i and p[i] (`safeInteger(p[i])`)
//
// with n an integer literal, x a parameter and f a field name: a path `p`
// reads the named data fields from the parameter in turn, each a required
// field of the record type the path before it has. A value term `p` is a
// path the clause states a safe integer; `p.length` is the length of an
// array or the length of a typed array the path's type names. Each
// atom's meaning is the index facts it elaborates to: `safeInteger(x)` is
// `int(x)`, `safeInteger(p.f)` the fact `p.f ≤ 2^53 - 1`, which holds of a
// path exactly where it reads a safe integer; a comparison is the linear fact
// over the integers its terms denote (`HeapKnowledge.Term`, a root position,
// a path and a kind), with every sum, difference and product it computes
// stated a safe integer. Where those facts hold, each side of the comparison
// evaluates under JavaScript's arithmetic to that safe integer exactly, so the
// comparison's answer is the fact's. A guarded clause `G || K`
// (PROGRAM-TYPING.md, "Guarded clauses") wraps each fact `K` elaborates to in
// a guarded fact: it holds where `G`'s path reads the tag's value, or the
// fact holds; each path after a guard is resolved where the guard's test
// fails, its type without the tag (an optional field read as present where
// it is not `undefined`). A clause executes no property read: it states what
// the reads denote in the heap a call starts in. A quantified atom
// `forall i in p: B`, the clause's last, states its body of every index `i`
// below `p.length`, of its element `p[i]` and of the clause's other terms
// (PROGRAM-TYPING.md, "Quantified clauses"; `IndexFact.every`). Every other
// form of the draft's grammar (`old`, `result`, computed keys, a `||` after
// an atom, `!`) is refused with the clause's location, as is a path whose field no type
// resolves.
//
// A type invariant (PROGRAM-TYPING.md, "Type invariants") is an
// `@invariant C` tag of a type alias's or an interface's leading JSDoc, its
// clause in the same language over `this`'s field paths, each resolved
// through the declaration's own type or, for a sealed handle, the
// representation a `@representation R` tag beside it names. The declaration
// graph reads the tags of each declaration it collects; where a function
// declaration's parameter or result is of a type naming the record, the
// clause is elaborated with `this` at that parameter's call position, a
// conjunct of the precondition, or at the result's position `0`, a fact of
// its result (`typeInvariants`, fragment-statements.mts).
import * as ts from "typescript/unstable/ast";
import type { BodyFact, BodyVariable, GuardTag, IndexFact, LinearFact, LinearTerm } from "./declaration-types.mts";

/** What a path's type names: an array, whose `length` is its store's length;
 * a typed array, whose `length` is its typed-array length (`view`); a string,
 * whose `length` is its count of code units (`string`); a record or any other
 * value (`other`); or no type a field resolves (`null`). */
export type PathType = "array" | "view" | "string" | "other" | null;
/** The tags a clause's guards exclude of a path's prefix of `depth` fields,
 * where the clause holds past them. */
export type Excluded = (depth: number) => readonly GuardTag[];
/** A parameter a clause may name: its name, its call position, and the type
 * a path of fields read from it has (`at`, the parameter's own at `[]`), each
 * prefix's type without the tags `excluded` names, an optional field read
 * where `undefined` is excluded of it, or, at the path's end, where
 * `optionalLast`. */
export type ClauseParameter = { name: string; position: number;
  at: (path: readonly string[], excluded?: Excluded, optionalLast?: boolean) => PathType };

/** The text of each `@requires` tag of the last JSDoc comment (`/** … *\/`)
 * in a declaration's leading trivia, with each line's leading `*` removed. */
export function requiresTags(trivia: string): string[] {
  return tagsOf(trivia, "requires");
}

/** The text of each `@invariant` tag of the last JSDoc comment in a type
 * declaration's leading trivia, alike. */
export function invariantTags(trivia: string): string[] {
  return tagsOf(trivia, "invariant");
}

/** The text of each `@representation` tag of the last JSDoc comment in a
 * type declaration's leading trivia, alike. */
export function representationTags(trivia: string): string[] {
  return tagsOf(trivia, "representation");
}

/** Whether a parameter is a plain required name: no rest, default or `?`,
 * and no pattern. Its input slot holds the call's actual at its position. */
export function plainParameter(p: ts.ParameterDeclaration): boolean {
  return !p.dotDotDotToken && !p.initializer && !p.questionToken && ts.isIdentifier(p.name);
}

/** Whether a function's body writes no binding of the parameter `p`'s
 * name: no assignment, compound or logical assignment, update,
 * destructuring assignment or `for` head anywhere in it targets that name,
 * a same-named binding of a nested scope's included. The parameter's input
 * slot then holds the call's actual at every return (PROGRAM-TYPING.md,
 * "Type invariants"). */
export function parameterKept(p: ts.ParameterDeclaration, body: ts.Node | undefined): boolean {
  if (!ts.isIdentifier(p.name)) return false;
  if (body === undefined) return true;
  const name = p.name.text;
  const targets = (e: ts.Node): boolean => {
    while (ts.isParenthesizedExpression(e)) e = e.expression;
    if (ts.isIdentifier(e)) return e.text === name;
    if (ts.isArrayLiteralExpression(e)) return e.elements.some(targets);
    if (ts.isObjectLiteralExpression(e)) return e.properties.some((q) =>
      ts.isShorthandPropertyAssignment(q) ? ts.isIdentifier(q.name) && q.name.text === name
        : ts.isPropertyAssignment(q) ? targets(q.initializer)
        : ts.isSpreadAssignment(q) ? targets(q.expression) : false);
    if (ts.isSpreadElement(e)) return targets(e.expression);
    if (ts.isBinaryExpression(e) && e.operatorToken.kind === ts.SyntaxKind.EqualsToken) return targets(e.left);
    return false;
  };
  const writes = (n: ts.Node): boolean => {
    if (ts.isBinaryExpression(n) && n.operatorToken.kind >= ts.SyntaxKind.FirstAssignment &&
        n.operatorToken.kind <= ts.SyntaxKind.LastAssignment && targets(n.left)) return true;
    if ((ts.isPrefixUnaryExpression(n) || ts.isPostfixUnaryExpression(n)) &&
        (n.operator === ts.SyntaxKind.PlusPlusToken || n.operator === ts.SyntaxKind.MinusMinusToken) &&
        targets(n.operand)) return true;
    if ((ts.isForOfStatement(n) || ts.isForInStatement(n)) && !ts.isVariableDeclarationList(n.initializer) &&
        targets(n.initializer)) return true;
    return !!n.forEachChild((c) => writes(c) || undefined);
  };
  return !writes(body);
}

/** Which type invariants an importer reads of an imported function
 * declaration of the program's sources (`writtenImport`): by its
 * declaration's parameters in order, `this` included (`receiver`), those of
 * each plain required name's type, where it is not async, at its returns too
 * where its body writes no binding of its name (`kept`, `parameterKept`);
 * and its result type's, where it is not async. */
export type ImportedInvariants = { receiver: boolean; params: readonly boolean[]; kept: readonly boolean[]; result: boolean };

function tagsOf(trivia: string, name: string): string[] {
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
      current = tag[1] === name ? [tag[2] ?? ""] : null;
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
    const op = /^(===|!==|<=|>=|&&|\|\||[!<>+\-*().,:\[\]])/.exec(text.slice(i));
    if (op) { out.push({ k: "op", v: op[0] }); i += op[0].length; continue; }
    return `the clause has a character outside its language: ${c}`;
  }
  return out;
}

/** A linear expression: coefficients by term and a constant, a term a
 * parameter's name or `xs.length`, and the subexpressions JavaScript computes
 * on the way (`steps`), each a sum, difference or product. */
type Linear = { terms: Map<string, number>; constant: number; steps: Linear[] };
type Atom = { k: "safeInteger"; of: string } | { k: "compare"; op: string; left: Linear; right: Linear } |
  { k: "forall"; binder: string; array: string; body: Atom[] };
/** A guard `p === tag ||`, and a clause: its guards in order, then its
 * conjunction. */
type Guard = { path: string; tag: GuardTag };
type Clause = { guards: Guard[]; atoms: Atom[] };

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
  /** A clause: its guards `p === null ||`, `p === undefined ||`, then a
   * conjunction. */
  clause(): Clause {
    const guards: Guard[] = [];
    for (;;) {
      const saved = this.at;
      const g = this.guard();
      if (g === null) { this.at = saved; break; }
      guards.push(g);
    }
    return { guards, atoms: this.conjunction() };
  }
  private guard(): Guard | null {
    const x = this.peek();
    if (!x || x.k !== "name" || x.v === "safeInteger") return null;
    const path = this.variable();
    if (!this.isOp("===")) return null;
    this.at++;
    const v = this.take();
    if (!v || v.k !== "name" || (v.v !== "null" && v.v !== "undefined")) return null;
    if (!this.isOp("||")) return null;
    this.at++;
    return { path, tag: v.v };
  }
  conjunction(): Atom[] {
    const atoms = [this.atom()];
    while (atoms[atoms.length - 1]?.k !== "forall" && this.isOp("&&")) { this.at++; atoms.push(this.atom()); }
    if (!this.done()) throw new ClauseError("the clause is a conjunction of atoms (`&&`) after its guards (`p === null ||`, `p === undefined ||`), no other connective");
    return atoms;
  }
  private atom(): Atom {
    const t = this.peek();
    // `forall i in p: C`: the rest of the clause is its body.
    if (t && t.k === "name" && t.v === "forall") {
      this.at++;
      const binder = this.take();
      if (!binder || binder.k !== "name") throw new ClauseError("`forall` names its index");
      const word = this.take();
      if (!word || word.k !== "name" || word.v !== "in") throw new ClauseError("`forall i` is followed by `in` and an array's path");
      const array = this.variable();
      this.expect(":");
      const body = [this.atom()];
      while (this.isOp("&&")) { this.at++; body.push(this.atom()); }
      if (body.some(a => a.k === "forall")) throw new ClauseError("a `forall` body states no `forall`");
      return { k: "forall", binder: binder.v, array, body };
    }
    if (t && t.k === "name" && t.v === "safeInteger") {
      this.at++;
      this.expect("(");
      const x = this.peek();
      if (!x || x.k !== "name") throw new ClauseError("`safeInteger` takes a parameter's path");
      const of = this.element(this.variable());
      this.expect(")");
      return { k: "safeInteger", of };
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
  /** A path: a parameter and the field names read from it, `.`-separated. */
  private variable(): string {
    const x = this.take();
    if (!x || x.k !== "name") throw new ClauseError("a product is an integer literal times a parameter's path");
    const names = [x.v];
    while (this.isOp(".")) {
      this.at++;
      const f = this.take();
      if (!f || f.k !== "name") throw new ClauseError("a path reads named fields");
      names.push(f.v);
    }
    return names.join(".");
  }
  /** A path, or the element `p[i]` a path's array holds at a `forall`'s index. */
  private element(path: string): string {
    if (!this.isOp("[")) return path;
    this.at++;
    const i = this.take();
    if (!i || i.k !== "name") throw new ClauseError("an element is read at a `forall`'s index");
    this.expect("]");
    return `${path}[${i.v}]`;
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
        return computed({ terms: new Map([[this.element(this.variable()), t.v]]), constant: 0, steps: [] });
      }
      return { terms: new Map(), constant: t.v, steps: [] };
    }
    if (t.k === "name") return { terms: new Map([[this.element(this.variable()), 1]]), constant: 0, steps: [] };
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

/** The positions an index fact names. */
export function indexFactPositions(f: IndexFact): number[] {
  if ("guarded" in f) return [f.guarded.slot, ...indexFactPositions(f.guarded.body)];
  if ("index" in f) return [f.index.slot];
  if ("int" in f) return [f.int.slot];
  if ("length" in f) return [f.length.array, f.length.length];
  if ("bound" in f) return [f.bound.array, f.bound.index];
  if ("element" in f) return [f.element.value, f.element.array, f.element.index];
  if ("every" in f) return [f.every.slot, f.every.stop.slot, ...f.every.body.flatMap(F =>
    ("le" in F ? F.le.form : F.ne.form).flatMap(([x]) => typeof x === "string" ? [] : [x.free.t.slot]))];
  const F = f.linear.fact;
  return ("le" in F ? F.le.form : F.ne.form).map(([t]) => t.slot);
}

/** The names a clause's paths start at, each once, in order: every name not
read as a field, a `forall`'s index or the clause's own words. A loop
invariant's clause names the bindings in scope at the loop's head. */
export function clauseRoots(text: string): string[] {
  const ts = tokens(text);
  if (typeof ts === "string") return [];
  const words = new Set(["forall", "in", "safeInteger", "null", "undefined"]);
  const binders = new Set<string>();
  const roots: string[] = [];
  ts.forEach((t, i) => {
    const before = ts[i - 1];
    if (t.k !== "name") return;
    if (before?.k === "name" && before.v === "forall") { binders.add(t.v); return; }
    if (before?.k === "op" && before.v === ".") return;
    if (words.has(t.v) || binders.has(t.v) || roots.includes(t.v)) return;
    roots.push(t.v);
  });
  return roots;
}

/** The text of each `@invariant` tag of the last JSDoc comment in a loop
 * statement's leading trivia (a loop invariant), alike. */
export function loopInvariantTags(file: ts.SourceFile, loop: ts.Node): string[] {
  return tagsOf(file.text.slice(loop.pos, loop.getStart(file)), "invariant");
}

/** The declaration name of each of `names` in scope where `loop` starts: the
 * nearest enclosing declaration, a loop's own `for` initializer first, then
 * each enclosing block's statements before the loop, a `for` initializer
 * around it, and an enclosing function's parameters. A name declared in a
 * pattern is found by its identifier there. */
export function loopBindings(loop: ts.Node, names: readonly string[]): Map<string, ts.Identifier> {
  const found = new Map<string, ts.Identifier>();
  const take = (scope: Map<string, ts.Identifier>): void => {
    for (const [n, id] of scope) if (!found.has(n)) found.set(n, id);
  };
  const bound = (name: ts.BindingName, into: Map<string, ts.Identifier>): void => {
    if (ts.isIdentifier(name)) { if (names.includes(name.text)) into.set(name.text, name); return; }
    for (const e of name.elements) if (ts.isBindingElement(e) && e.name !== undefined) bound(e.name, into);
  };
  const declared = (list: ts.VariableDeclarationList, into: Map<string, ts.Identifier>): void => {
    for (const d of list.declarations) bound(d.name, into);
  };
  if (ts.isForStatement(loop) && loop.initializer && ts.isVariableDeclarationList(loop.initializer)) {
    const own = new Map<string, ts.Identifier>();
    declared(loop.initializer, own);
    take(own);
  }
  let child: ts.Node = loop;
  for (let n: ts.Node | undefined = loop.parent; n !== undefined; child = n, n = n.parent) {
    const scope = new Map<string, ts.Identifier>();
    if (ts.isBlock(n) || ts.isSourceFile(n) || ts.isCaseClause(n) || ts.isDefaultClause(n)) {
      for (const st of n.statements) {
        if (st === child) break;
        if (ts.isVariableStatement(st)) declared(st.declarationList, scope);
      }
    } else if (ts.isForStatement(n) && n.initializer && ts.isVariableDeclarationList(n.initializer)) {
      declared(n.initializer, scope);
    } else if (ts.isFunctionDeclaration(n) || ts.isFunctionExpression(n) || ts.isArrowFunction(n) ||
        ts.isMethodDeclaration(n) || ts.isConstructorDeclaration(n)) {
      for (const p of n.parameters) bound(p.name, scope);
    }
    take(scope);
  }
  return found;
}

/** The index facts a declaration's `@requires` clauses elaborate to, or the
 * reason one is refused. */
export function elaborateRequires(clauses: readonly string[], params: readonly ClauseParameter[]):
    { facts: IndexFact[] } | { refused: string } {
  try {
    const parsed = clauses.map(text => {
      const ts = tokens(text);
      if (typeof ts === "string") throw new ClauseError(ts);
      return new Parser(ts).clause();
    });
    if (parsed.some(c => c.guards.some(g => g.tag === "undefined")) && params.some(q => q.name === "undefined"))
      throw new ClauseError("the clause's `undefined` is shadowed by a parameter");
    const param = (name: string): ClauseParameter => {
      const p = params.find(q => q.name === name);
      if (!p) throw new ClauseError(`the clause names ${name}, which is no parameter of the declaration`);
      return p;
    };
    // The safe integers every clause states, then its comparisons' facts.
    const intFacts: IndexFact[] = [];
    const compared: IndexFact[] = [];
    /** The facts each atom of a clause states, each in turn in a guarded
     * fact of each of the clause's guards, the first outermost. */
    const elaborate = (clause: Clause, unguarded: ReadonlySet<string>): void => {
      const { guards, atoms } = clause;
      /** The tags the guards before the `i`-th exclude of the prefix of
       * `depth` fields of the parameter `x`'s path. */
      const excludedBy = (i: number, x: string): Excluded => (depth) =>
        guards.slice(0, i).flatMap(g => {
          const [y = "", ...fields] = g.path.split(".");
          return y === x && fields.length === depth ? [g.tag] : [];
        });
      /** The parameter and fields a path names, each field resolved past
       * the guards before the `i`-th. */
      const pathAt = (i: number, key: string, optionalLast = false): { p: ClauseParameter; path: string[] } => {
        const [x = "", ...fields] = key.split(".");
        const p = param(x);
        if (fields.length > 0 && p.at(fields, excludedBy(i, x), optionalLast) === null)
          throw new ClauseError(`the path ${key} reads a field no record type of ${x} declares as a required data field`);
        return { p, path: fields };
      };
      const resolved = guards.map((g, i) => {
        const { p, path: fields } = pathAt(i, g.path, g.tag === "undefined");
        return { slot: p.position, path: fields, tag: g.tag };
      });
      const wrap = (f: IndexFact): IndexFact =>
        resolved.reduceRight<IndexFact>((body, g) => ({ guarded: { ...g, body } }), f);
      const path = (key: string): { p: ClauseParameter; path: string[] } => pathAt(guards.length, key);
      const value = (key: string): LinearTerm => {
        const { p, path: fields } = path(key);
        return { kind: "value", slot: p.position, path: fields };
      };
      const ints = new Set([...unguarded,
        ...atoms.flatMap(a => a.k === "safeInteger" ? [JSON.stringify(value(a.of))] : [])]);
      const term = (key: string): LinearTerm => {
        const names = key.split(".");
        // `p.length` of an array, a typed array or a string path is its
        // length; of any other, the field `length` read from it.
        if (names.length > 1 && names[names.length - 1] === "length") {
          const prefix = names.slice(0, -1).join(".");
          const { p, path: fields } = path(prefix);
          const at = p.at(fields, excludedBy(guards.length, names[0] ?? ""));
          if (at === "array") return { kind: "length", slot: p.position, path: fields };
          if (at === "view") return { kind: "view", slot: p.position, path: fields };
          if (at === "string") return { kind: "strLength", slot: p.position, path: fields };
        }
        const t = value(key);
        if (!ints.has(JSON.stringify(t))) throw new ClauseError(`the comparison names ${key}, which the clause does not state a safe integer`);
        return t;
      };
      for (const a of atoms) {
        if (a.k !== "safeInteger") continue;
        const t = value(a.of);
        intFacts.push(wrap(t.path.length === 0 ? { int: { slot: t.slot } }
          : { linear: { fact: { le: { form: [[t, 1]], bound: MAX_SAFE } } } }));
      }
      /** The fact `Σ c·t ≤ bound`, each term once, sorted by position and kind. */
      const lessEq = (terms: Map<string, number>, bound: number): void => {
        if (!Number.isSafeInteger(bound)) throw new ClauseError("the clause's constants lie outside the safe integers");
        const form: [LinearTerm, number][] = [...terms].filter(([, c]) => c !== 0)
          .map(([x, c]): [LinearTerm, number] => [term(x), c])
          .sort((a, b) => order(a[0], b[0]));
        const fact: LinearFact = { le: { form, bound } };
        compared.push(wrap({ linear: { fact } }));
      };
      compareAtoms(atoms, lessEq);
      // `forall i in p: C` (PROGRAM-TYPING.md, "Quantified clauses"): for
      // every index of the array or typed array `p` reads, below its length
      // or its typed-array length, `C` holds of the index `i`, the element
      // `p[i]` and the clause's other terms; an element named in a
      // comparison is stated a safe integer by `safeInteger(p[i])`, as a
      // path is.
      for (const a of atoms) {
        if (a.k !== "forall") continue;
        const root = a.array.split(".")[0] ?? "";
        const { p, path: fields } = path(a.array);
        const ranged = p.at(fields, excludedBy(guards.length, root));
        if (ranged !== "array" && ranged !== "view")
          throw new ClauseError(`\`forall\` ranges over the indices of an array or a typed array, which ${a.array} is not`);
        if (params.some(q => q.name === a.binder)) throw new ClauseError(`the index ${a.binder} is a parameter's name`);
        const elem = `${a.array}[${a.binder}]`;
        const body: BodyFact[] = [];
        for (const b of a.body) {
          if (b.k !== "safeInteger") continue;
          if (b.of !== elem) throw new ClauseError(`a \`forall\` body states safeInteger(${elem}) alone`);
          body.push({ le: { form: [["elem", 1]], bound: MAX_SAFE } });
        }
        const variable = (key: string): BodyVariable => {
          if (key === a.binder) return "index";
          if (key === elem) {
            if (!a.body.some(b => b.k === "safeInteger")) throw new ClauseError(`the comparison names ${elem}, which the clause does not state a safe integer`);
            return "elem";
          }
          if (key.includes("[")) throw new ClauseError(`${key} is no element of the array ${a.array} at the index ${a.binder}`);
          return { free: { t: term(key) } };
        };
        compareAtoms(a.body, (terms, bound) => {
          if (!Number.isSafeInteger(bound)) throw new ClauseError("the clause's constants lie outside the safe integers");
          body.push({ le: { form: [...terms].filter(([, c]) => c !== 0).map(([x, c]): [BodyVariable, number] => [variable(x), c]),
            bound } });
        });
        compared.push(wrap({ every: { slot: p.position, path: fields,
          stop: { kind: ranged === "array" ? "length" : "view", slot: p.position, path: fields }, body } }));
      }
    };
    /** The values the unguarded clauses state safe integers. */
    const unguarded = new Set(parsed.filter(c => c.guards.length === 0).flatMap(c => c.atoms.flatMap(a => {
      if (a.k !== "safeInteger") return [];
      const [x = "", ...fields] = a.of.split(".");
      return [JSON.stringify({ kind: "value", slot: param(x).position, path: fields })];
    })));
    for (const c of parsed) elaborate(c, unguarded);
    const seen = new Set<string>();
    const facts = [...intFacts, ...compared].filter(f => {
      const key = JSON.stringify(f);
      return seen.has(key) ? false : (seen.add(key), true);
    });
    return { facts };
  } catch (e) {
    if (e instanceof ClauseError) return { refused: e.message };
    throw e;
  }
}

/** The facts the comparison atoms state (`lessEq`): each computed
 * subexpression a safe integer, then the comparison over the integers. */
function compareAtoms(atoms: readonly Atom[], lessEq: (terms: Map<string, number>, bound: number) => void): void {
    const compare = (l: Linear, r: Linear, strict: boolean): void => {
      const d = add(l, r, -1);
      lessEq(d.terms, -d.constant - (strict ? 1 : 0));
    };
    for (const a of atoms) {
      if (a.k !== "compare") continue;
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
}

const MAX_SAFE = Number.MAX_SAFE_INTEGER;

/** Terms in the order of a normal form (`HeapKnowledge.Term.before`): by
 * position and kind, a position's value, then its length, then its element
 * count, then its string's length; then by path, lexicographically, the empty
 * path first. */
function order(a: LinearTerm, b: LinearTerm): number {
  const kindCode = { value: 0, length: 1, view: 2, strLength: 3 } as const;
  const code = (t: LinearTerm): number => 4 * t.slot + kindCode[t.kind];
  if (code(a) !== code(b)) return code(a) - code(b);
  for (let i = 0; i < Math.min(a.path.length, b.path.length); i++) {
    const x = a.path[i] ?? "", y = b.path[i] ?? "";
    if (x !== y) return x < y ? -1 : 1;
  }
  return a.path.length - b.path.length;
}
