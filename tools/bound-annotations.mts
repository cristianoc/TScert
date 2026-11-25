// The preconditions of a function declaration (RFC #115, the draft
// docs/drafts/checked-bound-annotations.md; ARITHMETIC.md, 
// "Preconditions"): a `@requires C` tag of the declaration's leading JSDoc
// comment, read from the source text, its clause parsed here and elaborated
// to index facts at the call's positions (`HeapKnowledge.IndexFact`: 0 the
// receiver, i + 1 the i-th actual).
//
// The clause language read here combines linear atoms over the
// declaration's parameters, with linear disjunction and negation after guards:
//
//   K ::= G || K | C        G ::= p === null | p === undefined | p === true | p === false
//   C ::= C && C | C || C | !C | (C) | A | forall i in p: B | forall i < n of p: B
//   A ::= safeInteger(p) | E rel E | p !== p      rel ∈ { <, <=, >, >=, === }
//   E ::= n | p | p.length | n * p | n * p.length | E + E | E - E | -E | (E)
//   p ::= x | p.f
//   B ::= A' && B | A'      A' an atom over E, i, p[i], its paths and lengths
//
// with n an integer literal, x a parameter and f a field name: a path `p`
// reads the named data fields from the parameter in turn, each a required
// field of the record type the path before it has. A value term `p` is a
// path the clause states a safe integer, or whose type, past the clause's
// guards, is the verifier's `SafeInt` at every arm (`PathType` "int"): the
// comparison's facts state its integrality of themselves, and every call
// establishes them; `p.length` is the length of an
// array or the length of a typed array the path's type names. Each
// atom's meaning is the index facts it elaborates to: `safeInteger(x)` is
// `int(x)`, `safeInteger(p.f)` the fact `p.f ≤ 2^53 - 1`, which holds of a
// path exactly where it reads a safe integer; a comparison is the linear fact
// over the integers its terms denote (`HeapKnowledge.Term`, a root position,
// a path and a kind), with every sum, difference and product it computes
// stated a safe integer. Where those facts hold, each side of the comparison
// evaluates under JavaScript's arithmetic to that safe integer exactly, so the
// comparison's answer is the fact's. A guarded clause `G || K`
// (ARITHMETIC.md, "Guarded clauses") wraps each fact `K` elaborates to in
// a guarded fact: it holds where `G`'s path reads the tag's value, or the
// fact holds; each path after a guard is resolved where the guard's test
// fails, its type without the tag (an optional field read as present where
// it is not `undefined`). A clause executes no property read: it states what
// the reads denote in the heap a call starts in. A quantified atom
// `forall i in p: B`, the clause's last, states its body of every index `i`
// below `p.length`, of its element `p[i]` and of the clause's other terms
// (ARITHMETIC.md, "Quantified clauses"; `IndexFact.every`). `p !== q` of two
// paths whose types are arrays states that their arrays hold different
// spines (ARITHMETIC.md, "Spine separation"; `IndexFact.spineApart`); a path
// that may be a typed array, or is no array, is refused. Every other
// form of the draft's grammar (`old`, computed keys) is refused with the clause's location, as is a path whose field no type
// resolves. A postcondition uses the same language with `result` at position
// zero and parameters one position after their call positions. Its facts
// hold in the return heap. Unconditional precondition integrality clauses
// permit value terms; the return check proves every resulting fact.
//
// A type invariant (ARITHMETIC.md, "Type invariants") is an
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
import type { BodyFact, BodyVariable, ElemTarget, GuardTag, IndexBound, IndexFact, IndexShift, LinearFact, LinearTerm } from "./declaration-types.mts";

/** What a path's type names: an array, whose `length` is its spine's length;
 * a typed array, whose `length` is its typed-array length (`view`); a string,
 * whose `length` is its count of code units (`string`); a safe integer, each
 * arm of the type the verifier's `SafeInt` or a safe integer's literal
 * (`int`); a record or any other value (`other`); or no type a field
 * resolves (`null`). */
export type PathType = "array" | "view" | "string" | "int" | "other" | null;
/** The tags a clause's guards exclude of a path's prefix of `depth` fields,
 * where the clause holds past them. */
export type Excluded = (depth: number) => readonly GuardTag[];
/** A parameter a clause may name: its name, its call position, and the type
 * a path of fields read from it has (`at`, the parameter's own at `[]`), each
 * prefix's type without the tags `excluded` names, an optional field read
 * where `undefined` is excluded of it, or, at the path's end, where
 * `optionalLast`. */
/** A name a clause reads: its position, and, where the clause may read it in
 * the entry state (`old(…)`), the entry's position holding it. */
export type ClauseParameter = { name: string; position: number; entry?: number;
  at: (path: readonly string[], excluded?: Excluded, optionalLast?: boolean) => PathType };

/** The text of each `@requires` tag of the last JSDoc comment (`/** … *\/`)
 * in a declaration's leading trivia, with each line's leading `*` removed. */
export function requiresTags(trivia: string): string[] {
  return tagsOf(trivia, "requires");
}

/** The normal-return clauses of a function declaration. */
export function ensuresTags(trivia: string): string[] {
  return tagsOf(trivia, "ensures");
}

/** The leading JSDoc of a function literal or its binding statement.
 * A statement's clauses apply to each function literal it binds. */
export function closureRequiresTags(node: ts.Node): string[] {
  const file = node.getSourceFile();
  const own = requiresTags(file.text.slice(node.pos, node.getStart(file)));
  let owner = node;
  while (ts.isParenthesizedExpression(owner.parent)) owner = owner.parent;
  if (ts.isVariableDeclaration(owner.parent) && owner.parent.initializer === owner) {
    owner = owner.parent;
    if (ts.isVariableDeclarationList(owner.parent) && ts.isVariableStatement(owner.parent.parent)) owner = owner.parent.parent;
  }
  return [...new Set([...own, ...requiresTags(file.text.slice(owner.pos, owner.getStart(file)))])];
}

/** The text of each `@invariant` tag in the last leading JSDoc comment. */
export function invariantTags(trivia: string): string[] {
  return tagsOf(trivia, "invariant");
}

/** The text of each `@representation` tag of the last JSDoc comment in a
 * type declaration's leading trivia, alike. */
export function representationTags(trivia: string): string[] {
  return tagsOf(trivia, "representation");
}

/** Whether a precondition may name a parameter: a name, not a rest. An
 * optional or defaulted one is named at its call position, where its input
 * slot holds the call's actual, `undefined` where the call passes none; the
 * default replaces it in the body, after the entry (ARITHMETIC.md,
 * "Preconditions"). */
export function clauseParameterName(p: ts.ParameterDeclaration): boolean {
  return !p.dotDotDotToken && ts.isIdentifier(p.name);
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
 * slot then holds the call's actual at every return (ARITHMETIC.md,
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
 * and its result type's, where it is not async. Written postconditions carry
 * their clauses and parameter names, or null for an unsupported signature. */
export type ImportedInvariants = { receiver: boolean; params: readonly boolean[]; kept: readonly boolean[];
  result: boolean; ensures: readonly string[]; ensuresParameters: readonly string[] | null };

/** The JSDoc tags a program's annotations are written in (ANNOTATIONS.md):
 * every reader of a tag names it from this list, through `tagsOf` and
 * `statesTag`. */
export const annotationTags = ["requires", "ensures", "invariant", "representation", "stable"] as const;
export type AnnotationTag = (typeof annotationTags)[number];

/** Whether the last JSDoc comment in a leading trivia states the tag `name`,
 * a tag carrying no clause. */
export function statesTag(trivia: string, name: AnnotationTag): boolean {
  const open = trivia.lastIndexOf("/**");
  const close = open < 0 ? -1 : trivia.indexOf("*/", open + 3);
  return close >= 0 && new RegExp(`(^|[\\s*])@${name}\\b`).test(trivia.slice(open + 3, close));
}

function tagsOf(trivia: string, name: AnnotationTag): string[] {
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
    const hex = /^0[xX][0-9a-fA-F]+/.exec(text.slice(i));
    if (hex) {
      const v = Number(hex[0]);
      if (!Number.isSafeInteger(v)) return `the literal ${hex[0]} is no safe integer`;
      out.push({ k: "num", v }); i += hex[0].length; continue;
    }
    const num = /^\d+/.exec(text.slice(i));
    if (num) {
      const v = Number(num[0]);
      if (!Number.isSafeInteger(v)) return `the literal ${num[0]} is no safe integer`;
      out.push({ k: "num", v }); i += num[0].length; continue;
    }
    const name = /^[A-Za-z_$][\w$]*/.exec(text.slice(i));
    if (name) { out.push({ k: "name", v: name[0] }); i += name[0].length; continue; }
    const op = /^(===|!==|<=|>=|&&|\|\||[!<>+\-*&().,:\[\]])/.exec(text.slice(i));
    if (op) { out.push({ k: "op", v: op[0] }); i += op[0].length; continue; }
    return `the clause has a character outside its language: ${c}`;
  }
  return out;
}

/** A linear expression: coefficients by term and a constant, a term a
 * parameter's name or `xs.length`, and the subexpressions JavaScript computes
 * on the way (`steps`), each a sum, difference or product. */
type Linear = { terms: Map<string, number>; constant: number; steps: Linear[] };
type BoundExpr = { base: string | null; offset: number };
type Atom = { k: "safeInteger"; of: string } | { k: "compare"; op: string; left: Linear; right: Linear } |
  { k: "forall"; binder: string; array: string; start: BoundExpr | null; stop: BoundExpr | null; elemGuards: Guard[]; body: Atom[][] } |
  { k: "distinct"; left: string; right: string } |
  { k: "elemTag"; elem: string; tag: GuardTag; negated: boolean };
/** A guard `p === tag ||`, and a clause: its guards in order, then its
 * conjunction. */
type Guard = { path: string; tag: GuardTag };
type Clause = { guards: Guard[]; atoms: Atom[] };

class Parser {
  private at = 0;
  private readonly ts: Token[];
  private readonly indexExprs: Map<string, Linear>;
  constructor(ts: Token[], indexExprs: Map<string, Linear> = new Map()) { this.ts = ts; this.indexExprs = indexExprs; }
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
  clause(): Clause[] {
    const guards: Guard[] = [];
    for (;;) {
      const saved = this.at;
      const g = this.guard();
      if (g === null) { this.at = saved; break; }
      guards.push(g);
    }
    const alternatives = this.disjunction();
    if (!this.done()) throw new ClauseError("unexpected token after the clause");
    return alternatives.map(atoms => ({ guards, atoms }));
  }
  private disjunction(): Atom[][] {
    let out = this.booleanConjunction();
    while (this.isOp("||")) { this.at++; out = [...out, ...this.booleanConjunction()]; }
    if (out.length > 64) throw new ClauseError("the clause has more than 64 alternatives");
    return out;
  }
  private booleanConjunction(): Atom[][] {
    let out = this.booleanPrimary();
    while (this.isOp("&&")) {
      this.at++;
      const right = this.booleanPrimary();
      if (out.length * right.length > 64) throw new ClauseError("the clause has more than 64 alternatives");
      out = out.flatMap(a => right.map(b => [...a, ...b]));
    }
    return out;
  }
  private booleanPrimary(): Atom[][] {
    if (this.isOp("!")) {
      this.at++;
      const body = this.booleanPrimary();
      let out: Atom[][] = [[]];
      for (const conjunction of body) {
        const negated = conjunction.flatMap((a): Atom[] => {
          if (a.k === "elemTag") return [{ ...a, negated: !a.negated }];
          if (a.k !== "compare") throw new ClauseError("negation requires linear comparisons");
          const opposite: Record<string, string> = { "<": ">=", "<=": ">", ">": "<=", ">=": "<", "!==": "===" };
          if (a.op === "===") return [{ ...a, op: "<" }, { ...a, op: ">" }];
          const op = opposite[a.op];
          if (op === undefined) throw new ClauseError("unsupported negated comparison");
          return [{ ...a, op }];
        });
        if (out.length * negated.length > 64) throw new ClauseError("the clause has more than 64 alternatives");
        out = out.flatMap(a => negated.map(b => [...a, b]));
      }
      return out;
    }
    const saved = this.at;
    try { return [[this.atom()]]; }
    catch (e) {
      if (!(e instanceof ClauseError)) throw e;
      this.at = saved;
      if (!this.isOp("(")) throw e;
      this.at++;
      const out = this.disjunction();
      this.expect(")");
      return out;
    }
  }
  private guard(): Guard | null {
    const x = this.peek();
    if (!x || x.k !== "name" || x.v === "safeInteger") return null;
    const path = this.variable();
    const eq = this.isOp("===");
    const ne = !eq && this.isOp("!==");
    if (!eq && !ne) return null;
    this.at++;
    const v = this.take();
    if (!v || v.k !== "name" || (v.v !== "null" && v.v !== "undefined" && v.v !== "true" && v.v !== "false")) return null;
    if (!this.isOp("||")) return null;
    this.at++;
    const tag: GuardTag = eq ? v.v
      : v.v === "null" ? "notNull" : v.v === "undefined" ? "notUndefined" : v.v === "true" ? "notTrue" : "notFalse";
    return { path, tag };
  }
  private elemGuard(): Guard | null {
    const x = this.peek();
    if (!x || x.k !== "name" || x.v === "safeInteger") return null;
    const path = this.element(this.variable());
    if (!path.includes("[")) return null;
    if (!this.isOp("===")) return null;
    this.at++;
    const v = this.take();
    if (!v || v.k !== "name" || (v.v !== "null" && v.v !== "undefined" && v.v !== "true" && v.v !== "false")) return null;
    if (!this.isOp("||")) return null;
    this.at++;
    return { path, tag: v.v };
  }
  private atom(): Atom {
    const t = this.peek();
    // `forall [lo <=] i [< hi of | in] p: C`: the rest of the clause is its body.
    if (t && t.k === "name" && t.v === "forall") {
      this.at++;
      let start: BoundExpr | null = null;
      let binder: string;
      const first = this.peek();
      const next = this.ts[this.at + 1];
      if (first && first.k === "name" && ((next?.k === "name" && next.v === "in") || (next?.k === "op" && next.v === "<"))) {
        this.at++;
        binder = first.v;
      } else {
        start = this.boundExpr();
        this.expect("<=");
        const b = this.take();
        if (!b || b.k !== "name") throw new ClauseError("`forall` names its index after `<=`");
        binder = b.v;
      }
      const stop = this.isOp("<") ? (this.at++, this.boundExpr()) : null;
      const word = this.take();
      if (!word || word.k !== "name" || word.v !== (stop === null ? "in" : "of"))
        throw new ClauseError("`forall` expects `in P` or `< bound of P`");
      const array = this.variable();
      this.expect(":");
      const elemGuards: Guard[] = [];
      for (;;) {
        const saved = this.at;
        const g = this.elemGuard();
        if (g === null) { this.at = saved; break; }
        elemGuards.push(g);
      }
      const body = this.disjunction();
      if (body.some(bs => bs.some(a => a.k === "forall"))) throw new ClauseError("a `forall` body states no `forall`");
      return { k: "forall", binder, array, start, stop, elemGuards, body };
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
    // `p !== q` of two array paths (ARITHMETIC.md, "Spine separation"), or
    // `p[q] === tag` / `p[q] !== tag` on an indexed array element.
    if (t && t.k === "name") {
      const saved = this.at;
      const left = this.element(this.variable());
      if (this.isOp("!==")) {
        this.at++;
        const r = this.peek();
        if (left.includes("[")) {
          if (r && r.k === "name" && (r.v === "null" || r.v === "undefined" || r.v === "true" || r.v === "false")) {
            this.at++;
            return { k: "elemTag", elem: left, tag: r.v, negated: true };
          }
        } else if (r && r.k === "name") {
          const right = this.variable();
          if (!this.isOp("+") && !this.isOp("-") && !this.isOp("[") && !this.isOp("&"))
            return { k: "distinct", left, right };
        }
      } else if (left.includes("[") && this.isOp("===")) {
        this.at++;
        const r = this.peek();
        if (r && r.k === "name" && (r.v === "null" || r.v === "undefined" || r.v === "true" || r.v === "false")) {
          this.at++;
          return { k: "elemTag", elem: left, tag: r.v, negated: false };
        }
      }
      this.at = saved;
    }
    const left = this.sum();
    const op = this.take();
    if (!op || op.k !== "op" || !["<", "<=", ">", ">=", "===", "!=="].includes(op.v))
      throw new ClauseError("an atom compares two terms with <, <=, >, >=, === or !==");
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
  /** An affine interval bound: an integer literal `c` or `-c`, or a path /
   * `old(p)` optionally shifted by `+ c` or `- c`. */
  private boundExpr(): BoundExpr {
    const t = this.peek();
    if (!t) throw new ClauseError("the clause ends inside a `forall` bound");
    if (this.isOp("-")) {
      this.at++;
      const n = this.take();
      if (!n || n.k !== "num") throw new ClauseError("a `forall` bound after `-` expects an integer literal");
      return { base: null, offset: -n.v };
    }
    if (t.k === "num") {
      this.at++;
      return { base: null, offset: t.v };
    }
    const base = this.stop();
    let offset = 0;
    if (this.isOp("+") || this.isOp("-")) {
      const sign = this.isOp("+") ? 1 : -1;
      this.at++;
      const n = this.take();
      if (!n || n.k !== "num") throw new ClauseError("a `forall` bound offset expects an integer literal");
      offset = sign * n.v;
    }
    return { base, offset };
  }
  /** A prefix clause's base term: a path, or `old(p)`, the path read in the
   * entry state. */
  private stop(): string {
    const t = this.peek();
    if (t?.k === "name" && t.v === "old" && this.ts[this.at + 1]?.k === "op" && this.ts[this.at + 1]?.v === "(") {
      this.at += 2;
      const inner = this.variable();
      this.expect(")");
      return `old(${inner})`;
    }
    return this.variable();
  }
  /** A path, or the element `p[expr]` a path's array holds at an index path or an affine `forall` index. */
  private element(path: string): string {
    if (!this.isOp("[")) return path;
    this.at++;
    const idx = this.sum();
    this.expect("]");
    for (const k of idx.terms.keys()) {
      if (k.includes("[")) throw new ClauseError("an array index expression cannot contain another index");
    }
    const entries = [...idx.terms].filter(([, c]) => c !== 0);
    const only = entries.length === 1 ? entries[0] : undefined;
    let inside: string;
    if (only !== undefined && only[1] === 1 && idx.constant === 0) {
      inside = only[0];
    } else if (only !== undefined && only[1] === 1 && idx.constant > 0 && !only[0].includes(".")) {
      inside = `${only[0]}+${idx.constant}`;
    } else {
      const parts: string[] = [];
      for (const [k, c] of entries.sort(([a], [b]) => a < b ? -1 : a > b ? 1 : 0)) {
        parts.push(c === 1 ? k : c === -1 ? `-${k}` : `${c}*${k}`);
      }
      if (idx.constant !== 0 || parts.length === 0) parts.push(String(idx.constant));
      inside = parts.join("+");
    }
    this.indexExprs.set(inside, idx);
    let out = `${path}[${inside}]`;
    while (this.isOp(".")) {
      this.at++;
      const f = this.take();
      if (!f || f.k !== "name") throw new ClauseError("an element path reads named fields");
      out += `.${f.v}`;
    }
    return out;
  }
  private product(): Linear {
    if (this.isOp("-")) { this.at++; return scale(this.product(), -1); }
    if (this.isOp("(")) {
      this.at++;
      const e = this.sum();
      if (this.isOp("&")) {
        this.at++;
        const m = this.take();
        if (!m || m.k !== "num" || !Number.isInteger(m.v) || m.v < 0 || m.v >= 0x80000000)
          throw new ClauseError("a bitmask is a nonnegative 31-bit integer literal");
        this.expect(")");
        const entries = [...e.terms];
        const first = entries[0];
        if (e.constant !== 0 || entries.length !== 1 || first === undefined || first[1] !== 1)
          throw new ClauseError("`&` applies to a single term");
        if (first[0].includes("&")) throw new ClauseError("nested bitmasks are not supported");
        return { terms: new Map([[`${first[0]}&${m.v}`, 1]]), constant: 0, steps: [] };
      }
      this.expect(")");
      return e;
    }
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
    // `old(p)`: the term `p` in the entry state (ARITHMETIC.md, "Two-state
    // postconditions"), a path or its length.
    if (t.k === "name" && t.v === "old" && this.ts[this.at + 1]?.k === "op" && this.ts[this.at + 1]?.v === "(") {
      this.at += 2;
      const inner = this.variable();
      this.expect(")");
      return { terms: new Map([[`old(${inner})`, 1]]), constant: 0, steps: [] };
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

function bodyPositions(f: BodyFact): number[] {
  if ("guarded" in f) {
    const t = f.guarded.target;
    return [...("parallel" in t ? [t.parallel.slot, ...t.parallel.shift.terms.map(([x]) => x.slot)] : []), ...bodyPositions(f.guarded.body)];
  }
  if ("bodyEither" in f) return [...bodyPositions(f.bodyEither.left), ...bodyPositions(f.bodyEither.right)];
  if ("either" in f) return [...bodyPositions(f.either.left), ...bodyPositions(f.either.right)];
  return ("le" in f ? f.le.form : f.ne.form).flatMap(([x]) =>
    typeof x === "string" || "project" in x || "offset" in x ? []
      : "parallel" in x ? [x.parallel.slot, ...x.parallel.shift.terms.map(([t]) => t.slot)] : [x.free.t.slot]);
}

function isBodyClauseOnly(f: BodyFact): boolean {
  return "guarded" in f || "bodyEither" in f;
}

function splitMask(key: string): { base: string; mask: number | null } {
  const amp = key.indexOf("&");
  if (amp < 0) return { base: key, mask: null };
  const mask = Number(key.slice(amp + 1));
  if (!Number.isInteger(mask) || mask < 0 || mask >= 0x80000000)
    throw new ClauseError("a bitmask is a nonnegative 31-bit integer literal");
  return { base: key.slice(0, amp), mask };
}

/** The positions an index fact names. */
export function indexFactPositions(f: IndexFact): number[] {
  if ("either" in f) return [...indexFactPositions(f.either.left), ...indexFactPositions(f.either.right)];
  if ("guarded" in f) return [f.guarded.slot, ...indexFactPositions(f.guarded.body)];
  if ("index" in f) return [f.index.slot];
  if ("int" in f) return [f.int.slot];
  if ("pastSafe" in f) return [f.pastSafe.slot];
  if ("length" in f) return [f.length.array, f.length.length];
  if ("bound" in f) return [f.bound.array, f.bound.index];
  if ("element" in f) return [f.element.value, f.element.array, ...f.element.index.terms.map(([t]) => t.slot)];
  if ("fieldRead" in f) return [f.fieldRead.value, f.fieldRead.object];
  if ("every" in f) return [f.every.slot,
    ...(f.every.start.base === null ? [] : [f.every.start.base.slot]),
    ...(f.every.stop.base === null ? [] : [f.every.stop.base.slot]),
    ...f.every.body.flatMap(bodyPositions)];
  if ("atIndex" in f) return [f.atIndex.slot, ...f.atIndex.index.terms.map(([t]) => t.slot), ...bodyPositions(f.atIndex.body)];
  if ("spineApart" in f) return [f.spineApart.slot, f.spineApart.other];
  if ("elemSpineApart" in f) return [f.elemSpineApart.slot, f.elemSpineApart.other];
  if ("apart" in f) return [f.apart.slot, f.apart.other];
  if ("same" in f) return [f.same.slot, f.same.other];
  const F = f.linear.fact;
  return ("le" in F ? F.le.form : F.ne.form).map(([t]) => t.slot);
}

/** The names a clause's paths start at, each once, in order: every name not
read as a field, a `forall`'s index or the clause's own words. A loop
invariant's clause names the bindings in scope at the loop's head. */
export function clauseRoots(text: string): string[] {
  return rootsOf(text, false);
}

/** The names a clause's paths start at in the current state: outside
 * `old(…)`. */
export function clauseCurrentRoots(text: string): string[] {
  return rootsOf(text, true);
}

function rootsOf(text: string, current: boolean): string[] {
  const ts = tokens(text);
  if (typeof ts === "string") return [];
  const words = new Set(["forall", "in", "safeInteger", "null", "undefined", "true", "false"]);
  const binders = new Set<string>();
  const ofPositions = new Set<number>();
  for (let i = 0; i < ts.length; i++) {
    const t = ts[i];
    if (!t || t.k !== "name" || t.v !== "forall") continue;
    const colon = ts.findIndex((tok, j) => j > i && tok.k === "op" && tok.v === ":");
    const end = colon < 0 ? ts.length : colon;
    const first = ts[i + 1];
    const second = ts[i + 2];
    if (first?.k === "name" && ((second?.k === "name" && second.v === "in") || (second?.k === "op" && second.v === "<"))) {
      binders.add(first.v);
    } else {
      for (let j = i + 1; j + 1 < end; j++) {
        if (ts[j]?.k === "op" && ts[j]?.v === "<=") {
          const b = ts[j + 1];
          if (b?.k === "name") binders.add(b.v);
          break;
        }
      }
    }
    for (let j = i + 1; j + 1 < end; j++) {
      if (ts[j]?.k === "name" && ts[j]?.v === "of" && ts[j + 1]?.k === "name") ofPositions.add(j);
    }
  }
  const roots: string[] = [];
  /** The tokens inside `old(…)`, which read the entry state. */
  const inOld = new Set<number>();
  ts.forEach((t, i) => {
    if (t.k === "name" && t.v === "old" && ts[i + 1]?.k === "op" && ts[i + 1]?.v === "(") {
      inOld.add(i);
      for (let j = i + 2; j < ts.length && !(ts[j]?.k === "op" && ts[j]?.v === ")"); j++) inOld.add(j);
    }
  });
  ts.forEach((t, i) => {
    const before = ts[i - 1];
    if (t.k !== "name") return;
    if (t.v === "old" && inOld.has(i) && !inOld.has(i - 1)) return;
    if (current && inOld.has(i)) return;
    if (ofPositions.has(i)) return;
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

/** The facts a clause elaborates to, or its refusal. The optional entry
 * assumptions permit safe-integer value terms in postconditions; their facts
 * are not part of the result, whose facts the return obligation proves. */
export function elaborateRequires(clauses: readonly string[], params: readonly ClauseParameter[], assumptions: readonly string[] = []):
    { facts: IndexFact[] } | { refused: string } {
  try {
    const indexExprs = new Map<string, Linear>();
    const parsed = clauses.map(text => {
      const ts = tokens(text);
      if (typeof ts === "string") throw new ClauseError(ts);
      return new Parser(ts, indexExprs).clause();
    });
    if (parsed.flat().some(c => c.guards.some(g => g.tag === "undefined" || g.tag === "notUndefined")) && params.some(q => q.name === "undefined"))
      throw new ClauseError("the clause's `undefined` is shadowed by a parameter");
    const param = (name: string): ClauseParameter => {
      const p = params.find(q => q.name === name);
      if (!p) throw new ClauseError(`the clause names ${name}, which is no parameter of the declaration`);
      return p;
    };
    const parseElemKey = (key: string): { elem: string; array: string; index: string; tail: string[] } | null => {
      const open = key.indexOf("[");
      if (open < 0) return null;
      const close = key.indexOf("]", open + 1);
      if (close < 0) throw new ClauseError(`invalid indexed element ${key}`);
      const array = key.slice(0, open);
      const index = key.slice(open + 1, close);
      const idxLin = indexExprs.get(index);
      if (idxLin !== undefined) {
        const entries = [...idxLin.terms].filter(([, c]) => c !== 0);
        const only = entries.length === 1 ? entries[0] : undefined;
        if (only === undefined || only[1] !== 1 || idxLin.constant !== 0)
          throw new ClauseError(`element offset ${key} is only permitted inside \`forall\``);
      } else if (index.includes("+") || index.includes("-") || index.includes("*")) {
        throw new ClauseError(`element offset ${key} is only permitted inside \`forall\``);
      }
      const rest = key.slice(close + 1);
      if (rest !== "" && !rest.startsWith(".")) throw new ClauseError(`invalid indexed element path ${key}`);
      const tail = rest === "" ? [] : rest.slice(1).split(".");
      return { elem: key.slice(0, close + 1), array, index, tail };
    };
    const atomsMentionElem = (atoms: readonly Atom[], elem: string): boolean => atoms.some(a => {
      if (a.k === "safeInteger") return a.of === elem || a.of.startsWith(`${elem}.`);
      if (a.k === "elemTag") return a.elem === elem;
      if (a.k === "compare") {
        const has = (e: Linear): boolean => [...e.terms.keys()].some(k => k === elem || k.startsWith(`${elem}.`)) ||
          e.steps.some(has);
        return has(a.left) || has(a.right);
      }
      return false;
    });
    /** The tags the guards before the `i`-th exclude of the prefix of
     * `depth` fields of the parameter `x`'s path. */
    const excludedBy = (guards: readonly Guard[], i: number, x: string): Excluded => (depth) =>
      guards.slice(0, i).flatMap(g => {
        const [y = "", ...fields] = g.path.split(".");
        return y === x && fields.length === depth ? [g.tag] : [];
      });
    /** The parameter and fields a path names, each field resolved past
     * the guards before the `i`-th. */
    const pathAt = (guards: readonly Guard[], i: number, key: string, optionalLast = false): { p: ClauseParameter; path: string[] } => {
      const [x = "", ...fields] = key.split(".");
      const p = param(x);
      if (fields.length > 0 && p.at(fields, excludedBy(guards, i, x), optionalLast) === null)
        throw new ClauseError(`the path ${key} reads a field no record type of ${x} declares as a required data field`);
      return { p, path: fields };
    };
    /** The outer guard wrapper for a clause's disjunction. */
    const outerWrapper = (guards: readonly Guard[]): ((f: IndexFact) => IndexFact) => {
      const resolved = guards.map((g, i) => {
        const { p, path: fields } = pathAt(guards, i, g.path, g.tag === "undefined" || g.tag === "notUndefined");
        return { slot: p.position, path: fields, tag: g.tag };
      });
      return (f: IndexFact): IndexFact =>
        resolved.reduceRight<IndexFact>((body, g) => ({ guarded: { ...g, body } }), f);
    };
    /** The facts each atom of a clause states (unwrapped by outer guards, which
     * are applied once around the clause's disjunction). */
    const elaborate = (clause: Clause, unguarded: ReadonlySet<string>, elemGuards: ReadonlyMap<string, GuardTag>): IndexFact[] => {
      const { guards, atoms } = clause;
      const intFacts: IndexFact[] = [];
      const compared: IndexFact[] = [];
      const path = (key: string): { p: ClauseParameter; path: string[] } => pathAt(guards, guards.length, key);
      /** Whether a path's type, past the clause's guards, is a safe integer. */
      const integral = (key: string): boolean => {
        const { p, path: fields } = path(key);
        return p.at(fields, excludedBy(guards, guards.length, key.split(".")[0] ?? "")) === "int";
      };
      const value = (key: string): LinearTerm => {
        const { p, path: fields } = path(key);
        return { kind: "value", slot: p.position, path: fields };
      };
      const ints = new Set([...unguarded,
        ...atoms.flatMap(a => a.k === "safeInteger" && !a.of.includes("[") ? [JSON.stringify(value(a.of))] : [])]);
      const term = (rawKey: string): LinearTerm => {
        const { base: key, mask } = splitMask(rawKey);
        if (mask !== null) {
          const inner = term(key);
          if (inner.kind !== "value") throw new ClauseError("`&` applies to a numeric value term");
          return { ...inner, kind: { bitMask: { mask } } };
        }
        // `old(p)`: the term `p` read in the entry state, at the entry's
        // position holding `p`'s root.
        if (key.startsWith("old(") && key.endsWith(")")) {
          const inner = term(key.slice(4, -1));
          const root = param(key.slice(4, -1).split(".")[0] ?? "");
          if (root.entry === undefined) throw new ClauseError(`\`old(…)\` reads ${root.name} in the entry state, which the clause has none of`);
          return { ...inner, slot: root.entry, atEntry: true };
        }
        const names = key.split(".");
        // `p.length` of an array, a typed array or a string path is its
        // length; of any other, the field `length` read from it.
        if (names.length > 1 && names[names.length - 1] === "length") {
          const prefix = names.slice(0, -1).join(".");
          const { p, path: fields } = path(prefix);
          const at = p.at(fields, excludedBy(guards, guards.length, names[0] ?? ""));
          if (at === "array") return { kind: "length", slot: p.position, path: fields };
          if (at === "view") return { kind: "view", slot: p.position, path: fields };
          if (at === "string") return { kind: "strLength", slot: p.position, path: fields };
        }
        const t = value(key);
        if (!ints.has(JSON.stringify(t)) && !integral(key))
          throw new ClauseError(`the comparison names ${key}, which neither its type nor the clause states a safe integer`);
        return t;
      };
      const negElemTags = new Map<string, GuardTag[]>();
      for (const a of atoms) {
        if (a.k !== "elemTag") continue;
        if (!a.elem.endsWith("]"))
          throw new ClauseError("an element guard tests the indexed element itself (`p[q] !== tag`)");
        if (!a.negated)
          throw new ClauseError(`\`${a.elem} === ${a.tag}\` may only appear as a guard disjunction \`${a.elem} === ${a.tag} || ...\``);
        const list = negElemTags.get(a.elem) ?? [];
        if (!list.includes(a.tag)) list.push(a.tag);
        negElemTags.set(a.elem, list);
      }
      const guardedHere = [...elemGuards.keys()].filter(e => atomsMentionElem(atoms, e));
      if (guardedHere.length > 1)
        throw new ClauseError("a conjunction may reference at most one guarded indexed element");
      const activeGuardElem = guardedHere[0] ?? null;
      type ElemSpec = { elem: string; slot: number; path: string[]; index: LinearTerm; guard: GuardTag | null;
        p: ClauseParameter; elemExcl: Excluded };
      const elemSpecCache = new Map<string, ElemSpec>();
      const resolveElem = (elem: string): ElemSpec => {
        const cached = elemSpecCache.get(elem);
        if (cached !== undefined) return cached;
        const parsedElem = parseElemKey(elem);
        if (parsedElem === null || parsedElem.tail.length > 0) throw new ClauseError(`invalid indexed element ${elem}`);
        const root = parsedElem.array.split(".")[0] ?? "";
        const { p, path: fields } = path(parsedElem.array);
        const ranged = p.at(fields, excludedBy(guards, guards.length, root));
        if (ranged !== "array")
          throw new ClauseError(`indexed element \`${elem}\` requires an array, which ${parsedElem.array} is not`);
        const index = term(parsedElem.index);
        const guard = elemGuards.get(elem) ?? null;
        const extraTags: GuardTag[] = [...(negElemTags.get(elem) ?? []), ...(guard !== null ? [guard] : [])];
        const elemDepth = fields.length + 1;
        const baseExcl = excludedBy(guards, guards.length, root);
        const elemExcl: Excluded = (depth) => depth === elemDepth ? [...baseExcl(depth), ...extraTags] : baseExcl(depth);
        const spec: ElemSpec = { elem, slot: p.position, path: fields, index, guard, p, elemExcl };
        elemSpecCache.set(elem, spec);
        return spec;
      };
      const elemVar = (spec: ElemSpec, rawKey: string): BodyVariable => {
        const { base: key, mask } = splitMask(rawKey);
        const parsedKey = parseElemKey(key);
        if (parsedKey !== null) {
          if (parsedKey.elem !== spec.elem)
            throw new ClauseError("a comparison may index at most one array element");
          const fields = parsedKey.tail;
          const length = fields.at(-1) === "length";
          if (mask !== null && length) throw new ClauseError("`&` applies to a numeric value term");
          const fieldPath = length ? fields.slice(0, -1) : fields;
          const kind = spec.p.at([...spec.path, "[]", ...fieldPath], spec.elemExcl);
          if (length) {
            if (kind !== "array" && kind !== "view" && kind !== "string")
              throw new ClauseError(`the element path ${key} has no length contract`);
            return { project: { kind: kind === "array" ? "length" : kind === "view" ? "view" : "strLength", path: fieldPath } };
          }
          if (!atoms.some(b => b.k === "safeInteger" && b.of === key) && kind !== "int")
            throw new ClauseError(`the comparison names ${key}, which neither its type nor the clause states a safe integer`);
          if (mask !== null) {
            if (fieldPath.length > 0 && kind === null) throw new ClauseError(`the element path ${key} has no field contract`);
            return { project: { kind: { bitMask: { mask } }, path: fieldPath } };
          }
          if (fieldPath.length === 0) return "elem";
          if (kind === null) throw new ClauseError(`the element path ${key} has no field contract`);
          return { project: { kind: "value", path: fieldPath } };
        }
        return { free: { t: term(rawKey) } };
      };
      const usedNegElems = new Set<string>();
      for (const a of atoms) {
        if (a.k !== "safeInteger") continue;
        const pk = parseElemKey(a.of);
        const targetElem = pk !== null ? pk.elem : activeGuardElem;
        if (targetElem !== null) {
          if (activeGuardElem !== null && pk !== null && pk.elem !== activeGuardElem)
            throw new ClauseError("a guarded indexed-element clause may index only its guarded element");
          const spec = resolveElem(targetElem);
          const v = elemVar(spec, a.of);
          if (v === "elem" || (typeof v !== "string" && "project" in v)) usedNegElems.add(targetElem);
          intFacts.push({ atIndex: { slot: spec.slot, path: spec.path, index: { terms: [[spec.index, 1]], offset: 0 }, guard: spec.guard,
            body: { le: { form: [[v, 1]], bound: MAX_SAFE } } } });
          continue;
        }
        const t = value(a.of);
        intFacts.push(t.path.length === 0 ? { int: { slot: t.slot } }
          : { linear: { fact: { le: { form: [[t, 1]], bound: MAX_SAFE } } } });
      }
      /** The fact `Σ c·t ≤ bound` (or `≠ bound` when `ne`), each term once, sorted by position and kind. */
      const linearFact = (terms: Map<string, number>, bound: number, ne: boolean): void => {
        if (!Number.isSafeInteger(bound)) throw new ClauseError("the clause's constants lie outside the safe integers");
        const nonzero = [...terms].filter(([, c]) => c !== 0);
        const elems = [...new Set(nonzero.flatMap(([x]) => {
          const pk = parseElemKey(splitMask(x).base);
          return pk === null ? [] : [pk.elem];
        }))];
        if (elems.length > 1) throw new ClauseError("a comparison may index at most one array element");
        const targetElem = elems[0] ?? activeGuardElem;
        if (targetElem !== null) {
          if (activeGuardElem !== null && elems[0] !== undefined && elems[0] !== activeGuardElem)
            throw new ClauseError("a guarded indexed-element clause may index only its guarded element");
          const spec = resolveElem(targetElem);
          const form: [BodyVariable, number][] = nonzero.map(([x, c]): [BodyVariable, number] => [elemVar(spec, x), c]);
          if (form.some(([v]) => v === "elem" || (typeof v !== "string" && "project" in v))) usedNegElems.add(targetElem);
          compared.push({ atIndex: { slot: spec.slot, path: spec.path, index: { terms: [[spec.index, 1]], offset: 0 }, guard: spec.guard,
            body: ne ? { ne: { form, bound } } : { le: { form, bound } } } });
          return;
        }
        const form: [LinearTerm, number][] = nonzero
          .map(([x, c]): [LinearTerm, number] => [term(x), c])
          .sort((a, b) => order(a[0], b[0]));
        const fact: LinearFact = ne ? { ne: { form, bound } } : { le: { form, bound } };
        compared.push({ linear: { fact } });
      };
      compareAtoms(atoms, (terms, bound) => linearFact(terms, bound, false), (terms, bound) => linearFact(terms, bound, true));
      for (const elem of negElemTags.keys()) {
        if (!usedNegElems.has(elem))
          throw new ClauseError(`\`${elem} !== ...\` must accompany a comparison or \`safeInteger\` naming \`${elem}\``);
      }
      // `p !== q` (ARITHMETIC.md, "Spine separation"): the arrays the two
      // paths read hold different spines. Each side's type is an array: a
      // typed array's view may share its buffer with another view.
      for (const a of atoms) {
        if (a.k !== "distinct") continue;
        if (activeGuardElem !== null)
          throw new ClauseError("a guarded indexed-element clause cannot state `!==`");
        const side = (key: string): { slot: number; path: string[] } => {
          const { p, path: fields } = path(key);
          const at = p.at(fields, excludedBy(guards, guards.length, key.split(".")[0] ?? ""));
          if (at === "view") throw new ClauseError(`\`!==\` compares two arrays, and ${key} may be a typed array, whose buffer another view may share`);
          if (at !== "array") throw new ClauseError(`\`!==\` compares two arrays, and ${key} is not an array`);
          return { slot: p.position, path: fields };
        };
        const l = side(a.left), r = side(a.right);
        compared.push({ spineApart: { slot: l.slot, path: l.path, other: r.slot, otherPath: r.path } });
      }
      // `forall i in p: C` (ARITHMETIC.md, "Quantified clauses"): for
      // every index of the array or typed array `p` reads, below its length
      // or its typed-array length, `C` holds of the index `i`, the element
      // `p[i]` and the clause's other terms; an element named in a
      // comparison is stated a safe integer by `safeInteger(p[i])`, as a
      // path is.
      for (const a of atoms) {
        if (a.k !== "forall") continue;
        if (activeGuardElem !== null)
          throw new ClauseError("a guarded indexed-element clause cannot state `forall`");
        const root = a.array.split(".")[0] ?? "";
        const { p, path: fields } = path(a.array);
        const ranged = p.at(fields, excludedBy(guards, guards.length, root));
        if (ranged !== "array" && ranged !== "view")
          throw new ClauseError(`\`forall\` ranges over the indices of an array or a typed array, which ${a.array} is not`);
        if (params.some(q => q.name === a.binder)) throw new ClauseError(`the index ${a.binder} is a parameter's name`);
        if (a.elemGuards.some(g => g.tag === "undefined") && params.some(q => q.name === "undefined"))
          throw new ClauseError("the clause's `undefined` is shadowed by a parameter");
        const elem = `${a.array}[${a.binder}]`;
        const splitIndexed = (key: string): { arr: string; elemKey: string; elemPath: string[]; shift: IndexShift; isZero: boolean; constOffset: number | null } | null => {
          const open = key.indexOf("[");
          if (open < 0) return null;
          const close = key.indexOf("]", open + 1);
          if (close < 0) return null;
          const arr = key.slice(0, open);
          const inside = key.slice(open + 1, close);
          const rest = key.slice(close + 1);
          if (rest !== "" && !rest.startsWith(".")) return null;
          const lin = indexExprs.get(inside);
          if (lin === undefined) return null;
          if ((lin.terms.get(a.binder) ?? 0) !== 1) return null;
          if (!Number.isSafeInteger(lin.constant))
            throw new ClauseError("the index shift's constant lies outside the safe integers");
          const shiftTerms: [LinearTerm, number][] = [...lin.terms]
            .filter(([k, c]) => k !== a.binder && c !== 0)
            .map(([k, c]): [LinearTerm, number] => [term(k), c])
            .sort((x, y) => order(x[0], y[0]));
          const shift: IndexShift = { terms: shiftTerms, offset: lin.constant };
          const isZero = shiftTerms.length === 0 && lin.constant === 0;
          const constOffset = shiftTerms.length === 0 && lin.constant > 0 ? lin.constant : null;
          return { arr, elemKey: key.slice(0, close + 1), elemPath: rest === "" ? [] : rest.slice(1).split("."),
            shift, isZero, constOffset };
        };
        const resolvedElemGuards: { target: ElemTarget; elemKey: string; arrFields: string[]; elemPath: string[]; tag: GuardTag }[] = [];
        const elemExcludedBy = (limit: number, elemKey: string, arrRoot: string, arrFields: string[], elemPath: string[]): Excluded => (depth) =>
          depth <= arrFields.length
            ? excludedBy(guards, guards.length, arrRoot)(depth)
            : resolvedElemGuards.slice(0, limit).flatMap(g =>
                g.elemKey === elemKey && g.arrFields.length + 1 + g.elemPath.length === depth &&
                g.elemPath.every((field, i) => elemPath[i] === field) ? [g.tag] : []);
        for (const g of a.elemGuards) {
          const parsedElem = splitIndexed(g.path);
          if (parsedElem === null)
            throw new ClauseError(`the element guard ${g.path} must index an array at ${a.binder} (with unit coefficient)`);
          const { arr, elemKey, elemPath, shift, isZero } = parsedElem;
          const arrRoot = arr.split(".")[0] ?? "";
          const { p: ap, path: arrFields } = path(arr);
          const arrKind = ap.at(arrFields, excludedBy(guards, guards.length, arrRoot));
          if (arrKind !== "array" && arrKind !== "view")
            throw new ClauseError(`the element guard ${g.path} indexes ${arr}, which is not an array or a typed array`);
          if (ap.at([...arrFields, "[]", ...elemPath], elemExcludedBy(resolvedElemGuards.length, elemKey, arrRoot, arrFields, elemPath),
              g.tag === "undefined") === null)
            throw new ClauseError(`the element path ${g.path} has no field contract`);
          const target: ElemTarget = arr === a.array && isZero
            ? { self: { path: elemPath } }
            : { parallel: { slot: ap.position, path: arrFields, shift, elemPath } };
          resolvedElemGuards.push({ target, elemKey, arrFields, elemPath, tag: g.tag });
        }
        const wrapElem = (f: BodyFact): BodyFact =>
          resolvedElemGuards.reduceRight<BodyFact>((b, g) => ({ guarded: { target: g.target, tag: g.tag, body: b } }), f);
        const branchBody = (atoms: Atom[]): BodyFact[] => {
        if (atoms.some(b => b.k === "distinct")) throw new ClauseError("a `forall` body states no `!==`");
        const body: BodyFact[] = [];
        const variable = (rawKey: string): BodyVariable => {
          const { base: key, mask } = splitMask(rawKey);
          if (key === a.binder) {
            if (mask !== null) throw new ClauseError("`&` does not apply to a `forall` index");
            return "index";
          }
          const parsedElem = splitIndexed(key);
          if (parsedElem !== null) {
            const { arr, elemKey, elemPath: fullPath, shift, isZero, constOffset } = parsedElem;
            if (arr === a.array && constOffset !== null && fullPath.length === 0) {
              if (mask !== null) throw new ClauseError("`&` does not apply to an offset element");
              if (!atoms.some(b => b.k === "safeInteger" && b.of === key) && p.at([...fields, "[]"], excludedBy(guards, guards.length, root)) !== "int")
                throw new ClauseError(`the comparison names ${key}, which neither its type nor the clause states a safe integer`);
              return { offset: { delta: constOffset } };
            }
            const arrRoot = arr.split(".")[0] ?? "";
            const { p: ap, path: arrFields } = path(arr);
            const arrKind = ap.at(arrFields, excludedBy(guards, guards.length, arrRoot));
            if (arrKind !== "array" && arrKind !== "view")
              throw new ClauseError(`${key} indexes ${arr}, which is not an array or a typed array`);
            const length = fullPath.at(-1) === "length";
            if (mask !== null && length) throw new ClauseError("`&` applies to a numeric value term");
            const ep = length ? fullPath.slice(0, -1) : fullPath;
            const kind = ap.at([...arrFields, "[]", ...ep], elemExcludedBy(resolvedElemGuards.length, elemKey, arrRoot, arrFields, ep));
            if (length) {
              if (kind !== "array" && kind !== "view" && kind !== "string")
                throw new ClauseError(`the element path ${key} has no length contract`);
              const k = kind === "array" ? "length" : kind === "view" ? "view" : "strLength";
              return arr === a.array && isZero ? { project: { kind: k, path: ep } }
                : { parallel: { slot: ap.position, path: arrFields, shift, kind: k, elemPath: ep } };
            }
            if (mask !== null) {
              if (!(arrKind === "view" && ep.length === 0) &&
                  !atoms.some(b => b.k === "safeInteger" && b.of === key) && kind !== "int")
                throw new ClauseError(`the comparison names ${key}, which neither its type nor the clause states a safe integer`);
              if (ep.length > 0 && kind === null) throw new ClauseError(`the element path ${key} has no field contract`);
              const bm = { bitMask: { mask } } as const;
              return arr === a.array && isZero ? { project: { kind: bm, path: ep } }
                : { parallel: { slot: ap.position, path: arrFields, shift, kind: bm, elemPath: ep } };
            }
            if (!atoms.some(b => b.k === "safeInteger" && b.of === key) && kind !== "int")
              throw new ClauseError(`the comparison names ${key}, which neither its type nor the clause states a safe integer`);
            if (ep.length > 0 && kind === null) throw new ClauseError(`the element path ${key} has no field contract`);
            if (arr === a.array && isZero) return ep.length === 0 ? "elem" : { project: { kind: "value", path: ep } };
            return { parallel: { slot: ap.position, path: arrFields, shift, kind: "value", elemPath: ep } };
          }
          if (key.includes("[")) throw new ClauseError(`${key} is no element of an array at the index ${a.binder} (or a shifted index with unit coefficient)`);
          return { free: { t: term(rawKey) } };
        };
        for (const b of atoms) {
          if (b.k === "elemTag") {
            if (b.negated) throw new ClauseError("a `forall` body states no negated element tag (`!==`)");
            if (b.tag === "undefined" && params.some(q => q.name === "undefined"))
              throw new ClauseError("the clause's `undefined` is shadowed by a parameter");
            const parsedElem = splitIndexed(b.elem);
            if (parsedElem === null)
              throw new ClauseError(`the element tag ${b.elem} must index an array at ${a.binder}`);
            const { arr, elemKey, elemPath, shift, isZero } = parsedElem;
            const arrRoot = arr.split(".")[0] ?? "";
            const { p: ap, path: arrFields } = path(arr);
            const arrKind = ap.at(arrFields, excludedBy(guards, guards.length, arrRoot));
            if (arrKind !== "array" && arrKind !== "view")
              throw new ClauseError(`the element tag ${b.elem} indexes ${arr}, which is not an array or a typed array`);
            if (ap.at([...arrFields, "[]", ...elemPath], elemExcludedBy(resolvedElemGuards.length, elemKey, arrRoot, arrFields, elemPath),
                b.tag === "undefined") === null)
              throw new ClauseError(`the element path ${b.elem} has no field contract`);
            const target: ElemTarget = arr === a.array && isZero
              ? { self: { path: elemPath } }
              : { parallel: { slot: ap.position, path: arrFields, shift, elemPath } };
            body.push({ guarded: { target, tag: b.tag, body: { le: { form: [], bound: -1 } } } });
            continue;
          }
          if (b.k !== "safeInteger") continue;
          if (splitIndexed(b.of) === null)
            throw new ClauseError(`a quantified safe integer must name ${elem} or an element at ${a.binder}`);
          body.push({ le: { form: [[variable(b.of), 1]], bound: MAX_SAFE } });
        }
        compareAtoms(atoms, (terms, bound) => {
          if (!Number.isSafeInteger(bound)) throw new ClauseError("the clause's constants lie outside the safe integers");
          body.push({ le: { form: [...terms].filter(([, c]) => c !== 0).map(([x, c]): [BodyVariable, number] => [variable(x), c]),
            bound } });
        }, (terms, bound) => {
          if (!Number.isSafeInteger(bound)) throw new ClauseError("the clause's constants lie outside the safe integers");
          body.push({ ne: { form: [...terms].filter(([, c]) => c !== 0).map(([x, c]): [BodyVariable, number] => [variable(x), c]),
            bound } });
        });
          return body;
        };
        let body: BodyFact[] | undefined;
        for (const atoms of a.body) {
          const branch = branchBody(atoms);
          if (body === undefined) body = branch;
          else {
            if (body.length * branch.length > 1024) throw new ClauseError("a quantified clause expands to more than 1024 facts");
            body = body.flatMap(left => branch.map((right): BodyFact =>
              isBodyClauseOnly(left) || isBodyClauseOnly(right)
                ? { bodyEither: { left, right } }
                : { either: { left, right } }));
          }
        }
        body = (body ?? []).map(wrapElem);
        const resolveBound = (b: BoundExpr): IndexBound => ({ base: b.base === null ? null : term(b.base), offset: b.offset });
        const startBound: IndexBound = a.start === null ? { base: null, offset: 0 } : resolveBound(a.start);
        const stopBound: IndexBound = a.stop === null
          ? { base: { kind: ranged === "array" ? "length" : "view", slot: p.position, path: fields }, offset: 0 }
          : resolveBound(a.stop);
        compared.push({ every: { slot: p.position, path: fields, start: startBound, stop: stopBound, body } });
      }
      return [...intFacts, ...compared];
    };
    /** The values the unguarded clauses state safe integers. */
    const assumed = assumptions.map(text => {
      const ts = tokens(text);
      if (typeof ts === "string") throw new ClauseError(ts);
      return new Parser(ts).clause();
    });
    const unguarded = new Set([...parsed, ...assumed].filter(cs => cs.length === 1).flat().filter(c => c.guards.length === 0).flatMap(c => c.atoms.flatMap(a => {
      if (a.k !== "safeInteger" || a.of.includes("[")) return [];
      const [x = "", ...fields] = a.of.split(".");
      return [JSON.stringify({ kind: "value", slot: param(x).position, path: fields })];
    })));
    const result: IndexFact[] = [];
    for (const alternatives of parsed) {
      const elemGuards = new Map<string, GuardTag>();
      const bodyAlts: Clause[] = [];
      for (const c of alternatives) {
        const only = c.atoms.length === 1 ? c.atoms[0] : undefined;
        if (only !== undefined && only.k === "elemTag" && !only.negated) {
          if (!only.elem.endsWith("]"))
            throw new ClauseError("an element guard tests the indexed element itself (`p[q] === tag`)");
          if (elemGuards.has(only.elem))
            throw new ClauseError(`indexed element \`${only.elem}\` may have at most one guard tag`);
          elemGuards.set(only.elem, only.tag);
        } else {
          bodyAlts.push(c);
        }
      }
      if (elemGuards.size > 0 && bodyAlts.length === 0)
        throw new ClauseError("an element guard `p[q] === tag` requires an alternative over that element");
      for (const elem of elemGuards.keys()) {
        if (!bodyAlts.some(c => atomsMentionElem(c.atoms, elem)))
          throw new ClauseError(`element guard on \`${elem}\` has no alternative referencing \`${elem}\``);
      }
      const clauseWrap = outerWrapper(alternatives[0]?.guards ?? []);
      const branches = bodyAlts.map(c => elaborate(c, unguarded, elemGuards));
      const common = (branches[0] ?? []).filter(f => branches.every(bs => bs.some(g => JSON.stringify(f) === JSON.stringify(g))));
      result.push(...common.map(clauseWrap));
      const residual = branches.map(bs => bs.filter(f => !common.some(g => JSON.stringify(f) === JSON.stringify(g))));
      let distributed: IndexFact[] | undefined;
      for (const branch of residual) {
        if (distributed === undefined) distributed = branch;
        else {
          if (distributed.length * branch.length > 1024) throw new ClauseError("the clause expands to more than 1024 facts");
          distributed = distributed.flatMap(left => branch.map(right => ({ either: { left, right } })));
        }
      }
      result.push(...(distributed ?? []).map(clauseWrap));
    }
    const seen = new Set<string>();
    const facts = result.filter(f => {
      const key = JSON.stringify(f);
      return seen.has(key) ? false : (seen.add(key), true);
    });
    return { facts };
  } catch (e) {
    if (e instanceof ClauseError) return { refused: e.message };
    throw e;
  }
}

/** The facts the comparison atoms state (`lessEq`, `notEq`): each computed
 * subexpression a safe integer, then the comparison over the integers. */
function compareAtoms(atoms: readonly Atom[], lessEq: (terms: Map<string, number>, bound: number) => void,
    notEq: (terms: Map<string, number>, bound: number) => void): void {
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
      else if (op === "!==") { const d = add(left, right, -1); notEq(d.terms, -d.constant); }
      else { compare(left, right, false); compare(right, left, false); }
    }
}

const MAX_SAFE = Number.MAX_SAFE_INTEGER;

/** Terms in the order of a normal form (`HeapKnowledge.Term.before`): by
 * position and kind, a position's value, then its length, then its element
 * count, then its string's length, then bitmasks by mask value; then by path,
 * lexicographically, the empty path first. */
function order(a: LinearTerm, b: LinearTerm): number {
  const kindRank = (k: LinearTerm["kind"]): number =>
    typeof k !== "string" ? 4 + k.bitMask.mask
      : k === "value" ? 0 : k === "length" ? 1 : k === "view" ? 2 : 3;
  if (a.slot !== b.slot) return a.slot - b.slot;
  const kr = kindRank(a.kind) - kindRank(b.kind);
  if (kr !== 0) return kr;
  for (let i = 0; i < Math.min(a.path.length, b.path.length); i++) {
    const x = a.path[i] ?? "", y = b.path[i] ?? "";
    if (x !== y) return x < y ? -1 : 1;
  }
  return a.path.length - b.path.length;
}
