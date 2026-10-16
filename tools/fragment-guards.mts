/* Part of the trusted front end (fragment-parse.mts): user-defined type guards
 * (`x is T`) and assertion functions (`asserts x is T`).
 *
 * A guard's promise, that a `true` result (a normal completion) leaves its
 * argument a `T`, is an obligation on its body, which TypeScript does not
 * check. The guard is the function at its plain type, `boolean` (`void`), and
 * beside it a derived unit, its promise, whose body is the guard's with each
 * result replaced by the argument: `return e` is `if (e) return x; throw x;`
 * (`return (e, x)`, and `x` at the closing brace, for an assertion function),
 * claimed at `T`. The promise unit is checked like any other, so the
 * soundness theorem's conclusion about its result is the promise: the two
 * bodies take the same steps, and the guard returns `true` (completes)
 * exactly where the unit returns its argument.
 *
 * A call consumes the promise by testing the argument again: `T` is a union of
 * primitive kinds and literals, decided by a test of the value alone
 * (`typeof`, strict equality), which runs no code and whose answer no step
 * changes. So `g(a)` is `g(a) && q(a)`, and the statement `f(a);` is
 * `f(a); if (!q(a)) throw a;`, the same program wherever the promise holds;
 * the narrowing is the test's own. Each function is a method of the gate. */
import * as ts from "typescript/unstable/ast";
import type { ArrowFunction, FunctionDeclaration, FunctionExpression, ParameterDeclaration } from "typescript/unstable/ast";
import type { Atom } from "./claim.mts";
import type { TypeTerm } from "./declaration-types.mts";
import type { Expr, FunctionAst, Stmt, TypeofShape } from "./fragment.mts";
import type { Span } from "./span.mts";
import type { Gate } from "./fragment-parse.mts";
import { completes } from "./fragment-support.mts";

/** One test of a promise's union: the argument's `typeof`, or its strict
 * equality with a primitive singleton. */
export type PromiseTest = { typeof: TypeofShape } | { equal: Atom };

/** A guard's promise: the parameter it is about (`index` among the
 * declaration's parameters, `argument` among a call's actuals), the union it
 * names as tests, and the promise's type. */
export interface GuardPromise {
  asserts: boolean;
  index: number;
  argument: number;
  tests: PromiseTest[];
  type: TypeTerm;
  at: Span;
}

const OUTSIDE = "is admitted where its type is a union of primitive kinds and literals";

/** The name of a guard's promise unit, which no source identifier spells. */
export const promiseName = (guard: string): string => `%Promise:${guard}%`;

/** The promise a declaration's result annotation states, or null where it
 * states none. Refused: `this is T`, `asserts x` without a type, a generic
 * guard, a promise about a rest or defaulted parameter, and a `T` no test of
 * the value decides. */
export function guardPromise(this: Gate, node: FunctionDeclaration | ArrowFunction | FunctionExpression): GuardPromise | null {
  const gate: Gate = this;
  const p = node.type;
  if (!p || !ts.isTypePredicateNode(p)) return null;
  const name = p.parameterName;
  if (!ts.isIdentifier(name))
    gate.fail(p, "a guard on `this` (`this is T`) is outside the fragment: its promise is about a receiver, which a call passes in no slot the caller tests again");
  if (!p.type)
    gate.fail(p, "`asserts x` without a type is outside the fragment: it promises the argument truthy, which no test of a primitive kind states");
  if (node.typeParameters?.length)
    gate.fail(p, "a generic type guard is outside the fragment: its promise is at each instance, which no test of the argument decides");
  const index = node.parameters.findIndex((q) => ts.isIdentifier(q.name) && q.name.text === name.text);
  const param: ParameterDeclaration | undefined = node.parameters[index];
  if (!param) return gate.fail(p, "a guard's promise names one of its parameters");
  if (param.dotDotDotToken || param.initializer)
    gate.fail(p, "a guard's promise about a rest or defaulted parameter is outside the fragment: the parameter is not the argument a caller tests");
  const receiver = node.parameters[0];
  const argument = receiver && ts.isIdentifier(receiver.name) && receiver.name.text === "this" ? index - 1 : index;
  const type = gate.typeOf(p.type, p);
  const tests = promiseTests(gate, type, 0);
  if (!tests) return gate.fail(p.type, `a type guard's promise \`${name.text} is ${gate.text(p.type)}\` names a type no test of the argument decides: a promise ${OUTSIDE}`);
  return { asserts: !!p.assertsModifier, index, argument, tests, type, at: gate.span(p) };
}

/** The tests deciding membership of `term`, following non-generic
 * declarations; null where some part is no primitive kind or literal. */
function promiseTests(gate: Gate, term: TypeTerm, depth: number): PromiseTest[] | null {
  switch (term.k) {
    case "atom":
      switch (term.name) {
        case "string": case "number": case "bigint": case "symbol": case "boolean": case "undefined":
          return [{ typeof: term.name }];
        case "null": return [{ equal: { a: "null" } }];
        default: return null;
      }
    case "literal":
      switch (term.name) {
        case "string": return [{ equal: { a: "stringlit", v: term.text } }];
        case "number": return [{ equal: { a: "numberlit", v: term.text } }];
        case "bigint": return [{ equal: { a: "bigintlit", v: term.text } }];
        case "true": case "false": return [{ equal: { a: "booleanlit", v: term.name } }];
      }
      return null;
    case "union": {
      const parts = term.parts.map((part) => promiseTests(gate, part, depth));
      return parts.every((part) => part !== null) ? parts.flat() : null;
    }
    case "reference": {
      if (term.args.length || depth > 16) return null;
      const target = term.reference.target;
      const definition = gate.definitions.find((d) => d.declaration.module === target.module &&
        d.declaration.name === target.name && d.declaration.span[0] === target.span[0] &&
        d.declaration.span[1] === target.span[1]);
      return definition && !definition.parameters.length ? promiseTests(gate, definition.expression, depth + 1) : null;
    }
    default:
      return null;
  }
}

/** The result a guard's caller reads: a guard's `boolean`, an assertion
 * function's `void`. */
export function guardResult(promise: GuardPromise): TypeTerm {
  return { k: "atom", name: promise.asserts ? "void" : "boolean", span: promise.at };
}

/** Spans no node of `used` holds, inside `region`, one per call: the
 * synthetic nodes' claims need sites of their own. */
function freshSpans(gate: Gate, region: Span, used: Set<string>): () => Span {
  const [s, e] = region;
  const candidates: Span[] = [];
  for (let j = e - 1; j > s; j--) candidates.push([s, j]);
  for (let i = s + 1; i < e; i++) candidates.push([i, e]);
  for (let i = s + 1; i < e; i++) for (let j = e - 1; j > i; j--) candidates.push([i, j]);
  return () => {
    for (;;) {
      const next = candidates.shift();
      if (!next) return gate.fail(null, `a guard's promise has more tests than the call at [${s},${e}) has free sites for their claims`);
      const key = next.join(":");
      if (!used.has(key)) {
        used.add(key);
        return next;
      }
    }
  };
}

/** Every span a tree holds. */
function spansOf(tree: unknown, into = new Set<string>()): Set<string> {
  if (Array.isArray(tree)) {
    if (tree.length === 2 && typeof tree[0] === "number" && typeof tree[1] === "number") into.add(tree.join(":"));
    else for (const item of tree) spansOf(item, into);
  } else if (tree !== null && typeof tree === "object") for (const value of Object.values(tree)) spansOf(value, into);
  return into;
}

/** `q(a)`: the disjunction of the promise's tests of `a`. */
function promiseTest(promise: GuardPromise, actual: Extract<Expr, { k: "id" }>, fresh: () => Span): Expr {
  const read = (): Expr => ({ k: "id", pos: fresh(), name: actual.name });
  const one = (t: PromiseTest): Expr => "typeof" in t
    ? { k: "typeofTest", pos: fresh(), shape: t.typeof, equal: true, e: read() }
    : { k: "bin", pos: fresh(), op: "===", l: read(), r: { k: "lit", pos: fresh(), lit: t.equal } };
  const [first, ...more] = promise.tests;
  if (!first) throw Error("internal: a promise without tests");
  return more.reduce<Expr>((acc, t) => ({ k: "bin", pos: fresh(), op: "||", l: acc, r: one(t) }), one(first));
}

/** Statements with every `return` of the function itself rewritten by `f`,
 * through blocks, branches, loops and handlers; a closure's are its own. */
function mapReturns(ss: Stmt[], f: (s: Extract<Stmt, { k: "return" }>) => Stmt): Stmt[] {
  const go = (ss: Stmt[]): Stmt[] => ss.map((s): Stmt => {
    switch (s.k) {
      case "return": return f(s);
      case "if": return { ...s, then: go(s.then), else_: s.else_ && go(s.else_) };
      case "while": return { ...s, body: go(s.body), update: go(s.update) };
      case "block": case "forOf": return { ...s, body: go(s.body) };
      case "closing": return { ...s, close: go(s.close), body: go(s.body) };
      case "try": return { ...s, body: go(s.body), handler: s.handler && { ...s.handler, body: go(s.handler.body) },
        finalizer: s.finalizer && go(s.finalizer) };
      default: return s;
    }
  });
  return go(ss);
}

/** Whether `name` is written anywhere in `tree`, a closure's body included. */
function written(tree: unknown, name: string): boolean {
  if (Array.isArray(tree)) return tree.some((item) => written(item, name));
  if (tree === null || typeof tree !== "object") return false;
  const node: Record<string, unknown> = { ...tree };
  const target = node["target"];
  const names = (t: unknown): boolean => t !== null && typeof t === "object" && "k" in t && t.k === "id" &&
    "name" in t && t.name === name;
  if ((node["k"] === "assign" || node["k"] === "nullishAssign" || node["k"] === "forOf") && node["name"] === name) return true;
  if ((node["k"] === "update" || node["k"] === "logicalAssign") && names(target)) return true;
  if (node["k"] === "arrayAssign" && Array.isArray(node["targets"]) &&
      node["targets"].some((t: unknown) => t !== null && typeof t === "object" && "target" in t && names(t.target))) return true;
  return Object.values(node).some((value) => written(value, name));
}

/** Whether a function's own statements hold a `try`, a closure's aside. */
function tries(ss: Stmt[]): boolean {
  return ss.some((s) => {
    switch (s.k) {
      case "try": return true;
      case "if": return tries(s.then) || (s.else_ !== null && tries(s.else_));
      case "while": return tries(s.body) || tries(s.update);
      case "block": case "forOf": return tries(s.body);
      case "closing": return tries(s.close) || tries(s.body);
      default: return false;
    }
  });
}

/** A guard's promise unit: its parameters, its result the promise's type,
 * its body the guard's with each result replaced by the argument where the
 * guard returns `true`, or completes, and a throw where it returns `false`.
 * A statement's entry is at its start, which no other statement shares: one
 * replacing a `return` starts where it did, and the ones inside it one and
 * two places into its keyword, where no source statement does. */
export function promiseUnit(this: Gate, name: string, namePos: Span, params: FunctionAst["params"], body: Stmt[],
    strict: boolean, promise: GuardPromise, block: Span): FunctionAst {
  const gate: Gate = this;
  const param = params[promise.index];
  if (!param) return gate.fail(null, "internal: a promise names no parameter");
  if (written(body, param.name))
    gate.fail(null, `a type guard that assigns its parameter \`${param.name}\` is outside the fragment: its promise is about the argument, which the parameter then no longer holds`);
  if (!promise.asserts && tries(body))
    gate.fail(null, "a type guard whose body holds a `try` is outside the fragment: its promise unit throws where the guard returns `false`, which a handler there would catch");
  const used = spansOf(body);
  const x = (pos: Span): Expr => ({ k: "id", pos, name: param.name });
  const mapped = mapReturns(body, (s): Stmt => {
    const fresh = freshSpans(gate, s.pos, used);
    const [start, end] = s.pos;
    if (promise.asserts) return { ...s, e: { k: "comma", pos: fresh(), left: s.e, right: x(fresh()) } };
    return { k: "if", pos: s.pos, cond: s.e, then: [{ k: "return", pos: [start + 1, end], e: x(fresh()) }],
      else_: [{ k: "throw", pos: [start + 2, end], e: x(fresh()) }] };
  });
  // An assertion function that completes returns its argument there.
  const completion: Stmt[] = promise.asserts && completes(mapped)
    ? [{ k: "return", pos: [block[1] - 1, block[1]], e: x(freshSpans(gate, block, used)()) }] : [];
  return { name: promiseName(name), namePos, typeParams: [], params, retType: promise.type,
    body: [...mapped, ...completion], strict };
}

/** Every direct call of a guard of the file whose promised actual is a name,
 * rewritten to test that name again: `g(a)` is `g(a) && q(a)`, and the
 * statement `f(a);` is `f(a); if (!q(a)) throw a;`. Calls through any other
 * callee, or of another actual, are the plain calls they are. */
export function applyPromises<T>(this: Gate, tree: T): T {
  const gate: Gate = this;
  if (!gate.guards.size) return tree;
  const used = spansOf(tree);
  const call = (e: unknown): { promise: GuardPromise; actual: Extract<Expr, { k: "id" }>; pos: Span } | null => {
    if (e === null || typeof e !== "object" || !("k" in e) || e.k !== "apply") return null;
    if (!("callee" in e) || !("args" in e) || !("pos" in e) || "spreads" in e || "typeArgs" in e) return null;
    const callee = e.callee;
    if (callee === null || typeof callee !== "object" || !("k" in callee) || callee.k !== "id" ||
        !("name" in callee) || typeof callee.name !== "string") return null;
    const promise = gate.guards.get(callee.name);
    if (!promise || !Array.isArray(e.args)) return null;
    const actual: unknown = e.args[promise.argument];
    if (actual === null || typeof actual !== "object" || !("k" in actual) || actual.k !== "id" ||
        !("name" in actual) || typeof actual.name !== "string" || !("pos" in actual)) return null;
    const pos = e.pos;
    if (!Array.isArray(pos) || typeof pos[0] !== "number" || typeof pos[1] !== "number") return null;
    return { promise, actual: { k: "id", pos: [0, 0], name: actual.name }, pos: [pos[0], pos[1]] };
  };
  const go = (v: unknown): unknown => {
    if (Array.isArray(v)) return v.flatMap((item) => {
      // An assertion function's call as a statement.
      if (item !== null && typeof item === "object" && "k" in item && item.k === "effect" && "e" in item) {
        const found = call(item.e);
        if (found?.promise.asserts) {
          // A statement's entry is at its start, which no other statement
          // shares: the two start one and two places into the call, inside
          // its callee or at its parenthesis, where no source statement does.
          const [s, e] = found.pos;
          const fresh = freshSpans(gate, found.pos, used);
          const test: Stmt = { k: "if", pos: [s + 1, e], cond: { k: "not", pos: fresh(), e: promiseTest(found.promise, found.actual, fresh) },
            then: [{ k: "throw", pos: [s + 2, e], e: { k: "id", pos: fresh(), name: found.actual.name } }], else_: null };
          return [go(item), test];
        }
      }
      return [go(item)];
    });
    if (v === null || typeof v !== "object") return v;
    const rebuilt = Object.fromEntries(Object.entries(v).map(([key, value]) => [key, go(value)]));
    const found = call(v);
    if (!found || found.promise.asserts) return rebuilt;
    const fresh = freshSpans(gate, found.pos, used);
    return { k: "bin", pos: fresh(), op: "&&", l: rebuilt, r: promiseTest(found.promise, found.actual, fresh) };
  };
  // asserted: the rebuilt tree has the input's shape: every object is copied key by key, and a node is replaced only by a node of the same kind (a call by an `&&` expression, a statement by statements)
  return go(tree) as T;
}
