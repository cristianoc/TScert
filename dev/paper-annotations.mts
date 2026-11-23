// The paper's annotations in a source file, for the experimental prototype of
// docs/drafts/paper-rules-mode.md: each function's effect type parameters
// with their `AtMost<P>` bounds and the parameters whose types mention them,
// and each call that writes an instance of such a parameter, with the check
// of the instance against the bound (rule Inst). The ordinary front end reads
// none of this: `AtMost` is a local alias of `unknown` there.
//   node dev/paper-annotations.mts file.ts
import { existsSync, readdirSync, readFileSync } from "node:fs";
import { dirname, join, resolve } from "node:path";
import { close as closeParser, openText } from "../tools/fragment-parse.mts";
import { syntax as ts } from "../tools/syntax.mts";
import { globalsOverlay } from "../tools/library-globals.mts";
import type { CallEffect } from "../tools/declaration-types.mts";

/** A change of the paper, in its order. */
const changes = ["keep", "init", "scalar", "extend", "grow", "any"] as const;
type Change = (typeof changes)[number];
const isChange = (s: string): s is Change => changes.some((c) => c === s);
const le = (a: Change, b: Change): boolean => changes.indexOf(a) <= changes.indexOf(b);

/** An effect of the paper: entries in the `Modifies` key syntax, and `else`;
for each reach entry `"x.**"` of a bound, its access paths (`reach`, by the
entry's key); and whether a class key (`values`, `spines`) was written,
which the effect reads into its `else`. Besides the `Modifies` keys, the
key `"x[#]"` names `x.cells`, the element locations of the array `x` holds,
as rule Elem-Write writes them. */
interface Effect { entries: [string, Change][]; else: Change; reach?: Record<string, AccJson>; classes?: boolean }

/** The access paths of a type, `Acc(T)` of "Declared reach": for each path
(field keys and `[*]` steps), the keys the type there declares and whether
it is an array (a spine and cells); `open` where some part of the type is a
form this script does not read, which may then declare any key. */
interface AccJson { paths: { path: string[]; keys: string[]; array: boolean }[]; open: boolean }

interface EffectParam { name: string; bound: Effect }
/** A function's effect parameters, its bounded callback parameters, and,
 * for a function with effect parameters, its own effect besides them (the
 * writes of its body other than its bounded callbacks' calls, keyed by its
 * parameters), or the reason it is not read. */
interface FunctionInfo {
  /** Its type parameters in order: an instance is the type argument at its
  effect parameter's position. */
  typeParams: string[];
  params: string[]; effectParams: EffectParam[]; bounded: { param: string; index: number; variable: string }[];
  own?: Effect | string;
  /** Why the function's own verdict cannot rest on its bounds: a bound or
  a callback's type is not read, or its own steps are not shown to keep the
  regions its bounds read (rule Bound's second premise). */
  refusal?: string;
  /** Why its signature is not read: a bound or a callback's type. A call
  of it is then refused too, since its calls' effects are not bounded. */
  unread?: string;
}
/** A call of a function with effect parameters: the instance, whether it is
 * within the bounds (rule Inst), and what the layer needs to give the call
 * its effect at the caller: the callee's parameters, the bounds, its own
 * effect besides them, and the call's source span, by which the layer
 * finds the call's node in the unit's source map. */
interface CallInfo {
  caller: string; callee: string; instance: Record<string, Effect>; ok: boolean; reason: string | null;
  params: string[]; bounds: Effect[]; own: Effect | string; span: [number, number];
}

/** An unsafe assume `paperAssume(a === b, "#n")`: the equality states a
 * fact the sound verifier should have established at the call, and the
 * issue tracks the verifier's extension. Its form is read here and its fact
 * added by the prototype's layer, under its axiom. */
interface AssumeInfo {
  /** The span of the assumed equality, whose step the layer extends. */
  caller: string; span: [number, number]; issue: string; line: number; ok: boolean; reason: string | null;
}

/** Whether an operand of an assumed equality is one the layer represents:
 * a variable, or a field read of one. */
function assumeOperand(e: ts.Expression): boolean {
  const u = unwrapExpr(e);
  return ts.isIdentifier(u) || (ts.isPropertyAccessExpression(u) && ts.isIdentifier(unwrapExpr(u.expression)));
}

/** An assume's form: `paperAssume(a === b, "#n")`, at most one operand a
 * field read; the reason otherwise. */
function assumeForm(n: ts.CallExpression): { issue: string } | string {
  const [fact, issue] = n.arguments;
  if (fact === undefined || issue === undefined || !ts.isStringLiteral(issue))
    return "an assume is written paperAssume(fact, \"#issue\")";
  const f = unwrapExpr(fact);
  if (!ts.isBinaryExpression(f) || f.operatorToken.kind !== ts.SyntaxKind.EqualsEqualsEqualsToken ||
      !assumeOperand(f.left) || !assumeOperand(f.right) ||
      (ts.isPropertyAccessExpression(unwrapExpr(f.left)) && ts.isPropertyAccessExpression(unwrapExpr(f.right))))
    return "an assumed fact is an equality of a variable and a variable or a field read of one";
  return { issue: issue.text };
}

/** The effect a string literal type `'{ "x[*]": "keep", "else": "any" }'`
 * holds as JSON. */
function effectOfText(text: string): Effect | null {
  let parsed: unknown;
  try { parsed = JSON.parse(text); } catch { return null; }
  if (typeof parsed !== "object" || parsed === null || Array.isArray(parsed)) return null;
  const entries: [string, Change][] = [];
  let otherwise: Change = "keep";
  let classes = false;
  for (const [key, value] of Object.entries(parsed)) {
    if (typeof value !== "string" || !isChange(value)) return null;
    // A class key bounds every location of its class: the effect read here
    // has no class regions, so it widens the `else` (each location is in one
    // class, and a change on a class the other key names is within the max).
    if (key === "values" || key === "spines") classes = true;
    if (key === "else" || key === "values" || key === "spines") { if (!le(value, otherwise)) otherwise = value; }
    else entries.push([key, value]);
  }
  return classes ? { entries, else: otherwise, classes } : { entries, else: otherwise };
}

/** The effect a type writes: a string literal type holding the paper's
 * literal as JSON (what the ordinary reader admits in a type argument), or
 * the literal itself, `{ "x[*]": "keep"; "else": "any" }`; null for any
 * other type. */
function effectOf(node: ts.TypeNode): Effect | null {
  if (ts.isLiteralTypeNode(node) && ts.isStringLiteral(node.literal)) return effectOfText(node.literal.text);
  if (!ts.isTypeLiteralNode(node)) return null;
  const entries: [string, Change][] = [];
  let otherwise: Change = "keep";
  let classes = false;
  for (const m of node.members) {
    if (!ts.isPropertySignatureDeclaration(m) || !m.type || !ts.isLiteralTypeNode(m.type)) return null;
    const literal = m.type.literal;
    if (!ts.isStringLiteral(literal) || !isChange(literal.text)) return null;
    const name = m.name;
    if ((ts.isIdentifier(name) || ts.isStringLiteral(name)) &&
        (name.text === "else" || name.text === "values" || name.text === "spines")) {
      // A class key widens the `else`, as in `effectOfText`.
      if (name.text !== "else") classes = true;
      if (!le(literal.text, otherwise)) otherwise = literal.text;
    } else if (ts.isStringLiteral(name)) entries.push([name.text, literal.text]);
    else return null;
  }
  return classes ? { entries, else: otherwise, classes } : { entries, else: otherwise };
}

/** The access paths of a type (`docs/drafts/effect-languages.md`, "Declared
reach"): `Acc(T)`, with the keys the type declares at each path and whether
it is an array there. Read are the members of a type literal or an
interface (its `extends` clauses too), the element type of an array, a
readonly array or `Array<T>`, a typed array (a spine and cells, no key), the
members of a union or an intersection, a primitive or literal type (no
key), and a type alias or interface named in the same file. Any other form
(a tuple, an index or call signature, a method, a mapped or conditional
type, a name declared elsewhere, a recursive reference) is open: it may
declare any key, so no key is decided absent from the reach. */
interface Acc { paths: Map<string, { keys: Set<string>; array: boolean }>; open: boolean }

function accOf(node: ts.TypeNode | undefined, decls: Map<string, ts.Node>): Acc {
  const acc: Acc = { paths: new Map(), open: false };
  const at = (path: string[]): { keys: Set<string>; array: boolean } => {
    const k = path.join(".");
    let e = acc.paths.get(k);
    if (e === undefined) { e = { keys: new Set(), array: false }; acc.paths.set(k, e); }
    return e;
  };
  const members = (ms: ts.NodeArray<ts.TypeElement>, path: string[], seen: string[]): void => {
    at(path);
    for (const m of ms) {
      if (ts.isPropertySignatureDeclaration(m) && (ts.isIdentifier(m.name) || ts.isStringLiteral(m.name))) {
        at(path).keys.add(m.name.text);
        walk(m.type, [...path, m.name.text], seen);
      } else acc.open = true;
    }
  };
  const named = (name: string, args: ts.NodeArray<ts.TypeNode> | undefined, path: string[], seen: string[]): void => {
    const decl = decls.get(name);
    if (decl === undefined) {
      if (/^(?:Uint8|Uint8Clamped|Int8|Uint16|Int16|Uint32|Int32|Float32|Float64)Array$/.test(name)) { at(path).array = true; return; }
      if ((name === "Array" || name === "ReadonlyArray") && args?.length === 1) {
        at(path).array = true;
        return walk(args[0], [...path, "[*]"], seen);
      }
      acc.open = true;
      return;
    }
    if (seen.includes(name) || (args ?? []).length > 0) { acc.open = true; return; }
    const inner = [...seen, name];
    if (ts.isTypeAliasDeclaration(decl) && (decl.typeParameters ?? []).length === 0) return walk(decl.type, path, inner);
    if (ts.isInterfaceDeclaration(decl) && (decl.typeParameters ?? []).length === 0) {
      for (const h of decl.heritageClauses ?? [])
        for (const t of h.types) {
          if (ts.isIdentifier(t.expression) && (t.typeArguments ?? []).length === 0) named(t.expression.text, undefined, path, inner);
          else acc.open = true;
        }
      return members(decl.members, path, inner);
    }
    acc.open = true;
  };
  const walk = (n: ts.TypeNode | undefined, path: string[], seen: string[]): void => {
    if (n === undefined) { acc.open = true; return; }
    switch (n.kind) {
      case ts.SyntaxKind.NumberKeyword: case ts.SyntaxKind.StringKeyword: case ts.SyntaxKind.BooleanKeyword:
      case ts.SyntaxKind.BigIntKeyword: case ts.SyntaxKind.SymbolKeyword: case ts.SyntaxKind.NullKeyword:
      case ts.SyntaxKind.UndefinedKeyword: case ts.SyntaxKind.VoidKeyword: case ts.SyntaxKind.NeverKeyword:
        return;
    }
    if (ts.isLiteralTypeNode(n)) return;
    if (ts.isParenthesizedTypeNode(n)) return walk(n.type, path, seen);
    if (ts.isUnionTypeNode(n) || ts.isIntersectionTypeNode(n)) { for (const t of n.types) walk(t, path, seen); return; }
    if (ts.isArrayTypeNode(n)) { at(path).array = true; return walk(n.elementType, [...path, "[*]"], seen); }
    if (ts.isTypeOperatorNode(n) && n.operator === ts.SyntaxKind.ReadonlyKeyword && ts.isArrayTypeNode(n.type))
      return walk(n.type, path, seen);
    if (ts.isTypeLiteralNode(n)) return members(n.members, path, seen);
    if (ts.isTypeReferenceNode(n) && ts.isIdentifier(n.typeName)) return named(n.typeName.text, n.typeArguments, path, seen);
    acc.open = true;
  };
  walk(node, [], []);
  return acc;
}

const accJson = (a: Acc): AccJson => ({
  paths: [...a.paths].map(([k, e]) => ({ path: k === "" ? [] : k.split("."), keys: [...e.keys].sort(), array: e.array })),
  open: a.open,
});
const accFromJson = (a: AccJson | undefined): Acc => a === undefined ? { paths: new Map(), open: true }
  : { paths: new Map(a.paths.map((e) => [e.path.join("."), { keys: new Set(e.keys), array: e.array }])), open: a.open };

/** The root variable of a region key: `xs` of `"xs[*]"`, `flow` of `"flow.data.**"`. */
const rootOf = (key: string): string => /^[A-Za-z_$][\w$]*/.exec(key)?.[0] ?? key;
/** Whether two keys name the same kind of region beyond their roots. */
const restOf = (key: string): string => key.slice(rootOf(key).length);

/** The names a type mentions as references. */
function mentions(node: ts.Node, out: Set<string>): void {
  if (ts.isTypeReferenceNode(node) && ts.isIdentifier(node.typeName)) out.add(node.typeName.text);
  node.forEachChild((c) => { mentions(c, out); return undefined; });
}

/** A variable's declaration, found by the language's scoping from a node:
 * the nearest enclosing block, function body or source file that declares
 * the name, or the nearest enclosing function whose parameter it is. */
type Decl =
  | { kind: "param"; owner: ts.Node; type: ts.TypeNode | undefined }
  | { kind: "const" | "let"; init: ts.Expression | undefined; type: ts.TypeNode | undefined; at: ts.Node }
  | { kind: "function"; node: ts.FunctionDeclaration };

function declIn(statements: readonly ts.Statement[], name: string): Decl | null {
  for (const st of statements) {
    if (ts.isVariableStatement(st)) {
      const list = st.declarationList;
      for (const d of list.declarations)
        if (ts.isIdentifier(d.name) && d.name.text === name)
          return { kind: (list.flags & ts.NodeFlags.Const) !== 0 ? "const" : "let", init: d.initializer, type: d.type, at: d };
    } else if (ts.isFunctionDeclaration(st) && st.name?.text === name) return { kind: "function", node: st };
  }
  return null;
}

/** A function-like node with parameters. */
type FnNode = ts.ArrowFunction | ts.FunctionExpression | ts.FunctionDeclaration | ts.MethodDeclaration;
const isFn = (n: ts.Node): n is FnNode =>
  ts.isArrowFunction(n) || ts.isFunctionExpression(n) || ts.isFunctionDeclaration(n) || ts.isMethodDeclaration(n);

function declOf(name: string, from: ts.Node): Decl | null {
  for (let n: ts.Node | undefined = from; n; n = n.parent) {
    if (ts.isBlock(n) || ts.isSourceFile(n) || ts.isModuleBlock(n)) {
      const d = declIn(n.statements, name);
      if (d) return d;
    }
    if (isFn(n))
      for (const p of n.parameters)
        if (ts.isIdentifier(p.name) && p.name.text === name) return { kind: "param", owner: n, type: p.type };
    if ((ts.isForOfStatement(n) || ts.isForInStatement(n) || ts.isForStatement(n)) && n.initializer &&
        ts.isVariableDeclarationList(n.initializer))
      for (const d of n.initializer.declarations)
        if (ts.isIdentifier(d.name) && d.name.text === name) return { kind: "let", init: undefined, type: d.type, at: d };
  }
  return null;
}

const within = (inner: ts.Node, outer: ts.Node): boolean => inner.pos >= outer.pos && inner.end <= outer.end;

/** A location expression, resolved: an object allocated by the closure
itself, whose own fields and spine are no effect on the caller's storage
(Fresh-Eff), or a path from a root variable of the caller's scope, with
every `const` alias of a path replaced by the path it holds
(`const ws = p.widths`: `ws` is `p.widths`); null where the path is not a
caller's variable's (the closure's parameter, an element, a call, or a
field of a fresh object, which may hold any older object). */
type Resolved = { fresh: true } | { fresh: false; root: string; path: string[] };

function unwrapExpr(e: ts.Expression): ts.Expression {
  while (ts.isParenthesizedExpression(e) || ts.isNonNullExpression(e) || ts.isAsExpression(e)) e = e.expression;
  return e;
}

const isAllocation = (e: ts.Expression | undefined): boolean =>
  e !== undefined && (ts.isObjectLiteralExpression(unwrapExpr(e)) || ts.isArrayLiteralExpression(unwrapExpr(e)));
const isPathExpr = (e: ts.Expression | undefined): e is ts.Expression => {
  if (e === undefined) return false;
  const u = unwrapExpr(e);
  return ts.isIdentifier(u) || (ts.isPropertyAccessExpression(u) && isPathExpr(u.expression));
};

function resolve_(expr: ts.Expression, closure: ts.Node | null, depth: number = 0, paramRoots: boolean = false): Resolved | null {
  const e = unwrapExpr(expr);
  if (depth > 32) return null;
  if (ts.isPropertyAccessExpression(e)) {
    const base = resolve_(e.expression, closure, depth + 1, paramRoots);
    if (base === null || base.fresh) return null;
    return { fresh: false, root: base.root, path: [...base.path, e.name.text] };
  }
  if (!ts.isIdentifier(e)) return null;
  const d = declOf(e.text, e);
  if (d === null || d.kind === "function") return null;
  const local = closure !== null && (d.kind === "param" ? d.owner === closure || within(d.owner, closure) : within(d.at, closure));
  // A function's own parameter is a root of its own effect (`paramRoots`);
  // a closure's parameter names no caller's storage.
  // A parameter its function assigns names, after the assignment, other
  // storage than its argument: no key of an effect read here.
  if (d.kind === "param")
    return (local && !(paramRoots && d.owner === closure)) || (closure !== null && assignedIn(e.text, d.owner)) ? null
      : { fresh: false, root: e.text, path: [] };
  if (d.kind === "const" && isPathExpr(d.init)) return resolve_(d.init, closure, depth + 1, paramRoots);
  if (local) return d.kind === "const" && isAllocation(d.init) ? { fresh: true } : null;
  return { fresh: false, root: e.text, path: [] };
}

/** The outermost function declaration enclosing a node: the unit whose
verdict carries a call's check. */
function unitOf(n: ts.Node): ts.FunctionDeclaration | null {
  let found: ts.FunctionDeclaration | null = null;
  for (let m: ts.Node | undefined = n.parent; m; m = m.parent)
    if (ts.isFunctionDeclaration(m) && m.parent !== undefined && ts.isSourceFile(m.parent)) found = m;
  return found;
}

/** Whether a parameter of a function is assigned anywhere in its body. */
function assignedIn(name: string, fn: ts.Node): boolean {
  let found = false;
  const visit = (n: ts.Node): undefined => {
    if (found) return undefined;
    const target = ts.isBinaryExpression(n) && n.operatorToken.kind >= ts.SyntaxKind.FirstAssignment &&
        n.operatorToken.kind <= ts.SyntaxKind.LastAssignment ? n.left
      : (ts.isPrefixUnaryExpression(n) || ts.isPostfixUnaryExpression(n)) &&
        (n.operator === ts.SyntaxKind.PlusPlusToken || n.operator === ts.SyntaxKind.MinusMinusToken) ? n.operand : undefined;
    if (target !== undefined && ts.isIdentifier(unwrapExpr(target)) && unwrapExpr(target).getText() === name) found = true;
    n.forEachChild(visit);
    return undefined;
  };
  fn.forEachChild(visit);
  return found;
}

/** Whether an object a `const` holds may be reached from other storage:
some reference to the binding (or to a `const` alias of it) is other than
the object of a member access (`x.f`, `x[i]`, `x.push(…)`), so it may be
stored, passed or returned. */
function escapes(decl: ts.VariableDeclaration, scope: ts.Node): boolean {
  if (!ts.isIdentifier(decl.name)) return true;
  const name = decl.name.text;
  let out = false;
  const visit = (n: ts.Node): undefined => {
    if (out) return undefined;
    if (ts.isIdentifier(n) && n.text === name && n !== decl.name) {
      const d = declOf(name, n);
      if (d !== null && d.kind === "const" && d.at === decl) {
        const p = n.parent;
        const member = p !== undefined && (ts.isPropertyAccessExpression(p) || ts.isElementAccessExpression(p)) && p.expression === n;
        const alias = p !== undefined && ts.isVariableDeclaration(p) && p.initializer === n &&
          (p.parent.flags & ts.NodeFlags.Const) !== 0;
        if (alias) { if (escapes(p, scope)) out = true; }
        else if (!member) out = true;
      }
    }
    n.forEachChild(visit);
    return undefined;
  };
  scope.forEachChild(visit);
  return out;
}

/** A key's root resolved at a call: the key with its root replaced by the
path an alias holds, and whether its root is an object the calling
function allocated: a `const` of its body initialised by an object or
array literal, never stored, passed or returned (Rule Alloc of Tolerant
frames gives its separation); null where the root resolves to nothing this
script reads. */
function normalizeKey(key: string, at: ts.Node, unit: ts.Node | null): { key: string; fresh: boolean } | null {
  const root = rootOf(key);
  const d = declOf(root, at);
  if (d === null || d.kind === "function") return null;
  if (d.kind === "const" && isPathExpr(d.init)) {
    const inner = d.init === undefined ? null : resolveAt(d.init);
    if (inner === null) return null;
    const head = [inner.root, ...inner.path].join(".");
    const fresh = inner.path.length === 0 && freshAt(inner.root, d.init ?? at, unit);
    return { key: head + restOf(key), fresh };
  }
  return { key, fresh: freshAt(root, at, unit) };
}

/** Whether a variable, read at a node, holds an object the unit allocated
in its body and never let escape. */
function freshAt(name: string, at: ts.Node, unit: ts.Node | null): boolean {
  const d = declOf(name, at);
  if (unit === null || d === null || d.kind !== "const" || !isAllocation(d.init) || !within(d.at, unit)) return false;
  return ts.isVariableDeclaration(d.at) && !escapes(d.at, unit);
}

function resolveAt(e: ts.Expression): { root: string; path: string[] } | null {
  const r = resolve_(e, null);
  return r === null || r.fresh ? null : r;
}

/** A call's argument as a path, its `const` aliases resolved; null for any
other expression. */
function argPath(e: ts.Expression): string | null {
  if (!isPathExpr(e)) return null;
  const r = resolveAt(e);
  return r === null ? null : [r.root, ...r.path].join(".");
}

/** A region key, parsed: its root, the declared keys from the root to the
location's object, and what it names there: a field, every field (`.*`),
the spine (`[*]`), the cells (`[#]`), or the reach through declared keys
(`.**`). */
interface Loc { root: string; path: string[]; kind: "field" | "fields" | "spine" | "cells" | "reach"; key: string | null }

function locOf(key: string): Loc | null {
  const m = /^([A-Za-z_$][\w$]*)((?:\.[A-Za-z_$][\w$]*)*)(\.\*\*|\.\*|\[\*\]|\[#\])?$/.exec(key);
  if (!m || m[1] === undefined) return null;
  const steps = (m[2] ?? "").split(".").filter((x) => x !== "");
  const tail = m[3];
  if (tail === ".**") return { root: m[1], path: steps, kind: "reach", key: null };
  if (tail === ".*") return { root: m[1], path: steps, kind: "fields", key: null };
  if (tail === "[*]") return { root: m[1], path: steps, kind: "spine", key: null };
  if (tail === "[#]") return { root: m[1], path: steps, kind: "cells", key: null };
  const last = steps.pop();
  return last === undefined ? null : { root: m[1], path: steps, kind: "field", key: last };
}

const pathText = (l: Loc): string => [l.root, ...l.path].join(".");

/** Whether a field key is declared anywhere in a reach. */
const declaresKey = (acc: Acc, key: string): boolean => [...acc.paths.values()].some((e) => e.keys.has(key));

/** Whether two locations are disjoint, decided from the source
(docs/drafts/effect-languages.md, "Decisions"): a field location, a spine
and cells differ (their keys differ); two field locations at different
keys differ whatever objects they are on (disjointness by key); a field
whose key no type in a closed reach declares lies outside it; and an own
location (a field or the spine, at the empty path) of an object the caller
allocated is apart from an own location of a parameter the caller never
assigns, and, where the object never escapes, from the parameter's reach
(rule Alloc of Tolerant frames). Anything else may overlap. `acc` is the
reach's access paths where one of them is a reach. */
function disjoint(r: Loc, b: Loc, acc: Acc, fresh: Set<string>, params: Set<string>): boolean {
  const ownOf = (l: Loc): boolean => l.path.length === 0 && (l.kind === "field" || l.kind === "fields" || l.kind === "spine");
  const apart = (f: Loc, o: Loc): boolean => fresh.has(f.root) && ownOf(f) && f.root !== o.root && params.has(o.root) &&
    o.path.length === 0 && (ownOf(o) || o.kind === "reach");
  if (apart(r, b) || apart(b, r)) return true;
  if (b.kind === "reach") return r.kind === "field" && r.key !== null && !acc.open && !declaresKey(acc, r.key);
  if (r.kind === "reach") return b.kind === "field" && b.key !== null && !acc.open && !declaresKey(acc, b.key);
  if (r.kind === "field" && b.kind === "field") return r.key !== b.key;
  const pair = new Set<Loc["kind"]>([r.kind, b.kind]);
  const differ = (x: Loc["kind"], y: Loc["kind"]): boolean => pair.size === 2 && pair.has(x) && pair.has(y);
  return differ("field", "spine") || differ("field", "cells") || differ("spine", "cells") || differ("fields", "spine");
}

/** Whether `r` lies in `b`: the same location, or a location at a path
`Acc(T)` admits when `b` is a reach. */
function inside(r: Loc, b: Loc, acc: Acc): boolean {
  if (b.kind === "reach") {
    const base = [b.root, ...b.path];
    const full = [r.root, ...r.path];
    if (full.length < base.length || base.some((x, i) => full[i] !== x)) return false;
    const e = acc.paths.get(full.slice(base.length).join("."));
    if (e === undefined) return false;
    if (r.kind === "field") return r.key !== null && e.keys.has(r.key);
    return (r.kind === "spine" || r.kind === "cells") && e.array;
  }
  return r.kind === b.kind && r.key === b.key && pathText(r) === pathText(b);
}

/** The function declaration a name imported by name from a relative module
 * names, read from that module. */
const importedFiles = new Map<string, ts.SourceFile>();
/** Whether a reviewed effect keeps every old location at a normal return:
 * each entry of its normal frame at `keep` (an empty footprint). */
const keepsHeap = (e: CallEffect): boolean => e.exits.normal.frame.every((f) => f.change === "keep");

/** The functions whose effect is being read, so a recursive call is refused. */
const reading = new Set<ts.Node>();
function importedDecl(name: string, from: ts.Node): ts.FunctionDeclaration | undefined {
  const sf = from.getSourceFile();
  for (const st of sf.statements) {
    if (!ts.isImportDeclaration(st) || !ts.isStringLiteral(st.moduleSpecifier)) continue;
    const named = st.importClause?.namedBindings;
    if (!named || !ts.isNamedImports(named) || !named.elements.some((e) => !e.isTypeOnly && e.name.text === name)) continue;
    const file = importedFile(sf.fileName, st.moduleSpecifier.text);
    if (file === null) return undefined;
    let tree = importedFiles.get(file);
    if (tree === undefined) { tree = openText(file, readFileSync(file, "utf8")); importedFiles.set(file, tree); }
    for (const d of tree.statements) if (ts.isFunctionDeclaration(d) && d.name?.text === name && d.body) return d;
  }
  return undefined;
}

/** A function's effect parameters: its type parameters bounded by `AtMost`. */
function effectVars(fn: FnNode): string[] {
  return (fn.typeParameters ?? []).filter((tp) => {
    const c = tp.constraint;
    return c !== undefined && ts.isTypeReferenceNode(c) && ts.isIdentifier(c.typeName) && c.typeName.text === "AtMost";
  }).map((tp) => tp.name.text);
}

/** The parameters of a function whose types mention one of its effect
 * parameters: its bounded callbacks. */
function boundedParams(fn: FnNode): Set<string> {
  const vars = effectVars(fn);
  const out = new Set<string>();
  for (const p of fn.parameters) {
    const seen = new Set<string>();
    if (p.type) mentions(p.type, seen);
    if (ts.isIdentifier(p.name) && vars.some((v) => seen.has(v))) out.add(p.name.text);
  }
  return out;
}

/** A closure's effect on its caller's storage, read from its body by the
 * paper's rules for steps (Section "Rules for steps"): a field write
 * `x.f = e` is `x.f: any` (Field-Write), as are a logical assignment
 * (`??=`, `||=`, `&&=`) and `+=`, which may write or keep a non-primitive
 * value; an arithmetic compound write or an increment of a field is
 * `x.f: scalar` (Field-Write-Scalar: strict TypeScript admits only number
 * and bigint operands there, and the fragment refuses `any`); an element
 * write `x[i] = e` is `x[*]: grow, x[#]: any`, the spine and the cells
 * (Elem-Write); `x.push(…)` of an `x` declared an array is
 * `x[*]: extend` (Push); a call of a function declared with a result
 * `Modifies<P, T>` is `P` at its arguments (Call). Storage the closure
 * allocates is no part of it (Fresh-Eff). The steps read are those of its
 * parameters' defaults and of its body. Any other step that may write (an
 * assignment to a captured binding or to a named member of an array,
 * another call, `delete` of an unnamed location, `new`) cannot be bounded
 * here: the result names it. */
/** The compound assignments whose old and new contents are numbers or
bigints in strict TypeScript. */
const arithmetic = new Set<ts.SyntaxKind>([
  ts.SyntaxKind.MinusEqualsToken, ts.SyntaxKind.AsteriskEqualsToken, ts.SyntaxKind.AsteriskAsteriskEqualsToken,
  ts.SyntaxKind.SlashEqualsToken, ts.SyntaxKind.PercentEqualsToken, ts.SyntaxKind.LessThanLessThanEqualsToken,
  ts.SyntaxKind.GreaterThanGreaterThanEqualsToken, ts.SyntaxKind.GreaterThanGreaterThanGreaterThanEqualsToken,
  ts.SyntaxKind.AmpersandEqualsToken, ts.SyntaxKind.BarEqualsToken, ts.SyntaxKind.CaretEqualsToken,
]);

/** The bounded callback parameters of a function, whose calls a closure's
effect leaves to the effect variable: the names and the function owning
them, so a call is skipped only where its callee resolves to one of them. */
interface Skip { owner: ts.Node | null; names: ReadonlySet<string> }
const noSkip: Skip = { owner: null, names: new Set() };

/** The type declarations of a file, read once per file. */
const typeDeclsOf = new Map<ts.SourceFile, Map<string, ts.Node>>();
function typeDecls(sf: ts.SourceFile): Map<string, ts.Node> {
  let m = typeDeclsOf.get(sf);
  if (m === undefined) {
    m = new Map();
    for (const s of sf.statements) if (ts.isTypeAliasDeclaration(s) || ts.isInterfaceDeclaration(s)) m.set(s.name.text, s);
    typeDeclsOf.set(sf, m);
  }
  return m;
}

/** Whether a location expression's value is an array by its declaration: a
root bound to an array literal, or a root whose declared type is closed and,
at the path, an array and nothing else (`Acc(T)`). */
function isArrayAt(r: { root: string; path: string[] }, at: ts.Node): boolean {
  const d = declOf(r.root, at);
  if (d === null || d.kind === "function") return false;
  if (r.path.length === 0 && d.kind !== "param" && d.type === undefined) return isArrayLiteral(d.init);
  const acc = accOf(d.type, typeDecls(at.getSourceFile()));
  const e = acc.paths.get(r.path.join("."));
  return !acc.open && e !== undefined && e.array && e.keys.size === 0;
}
/** Whether a location expression's value is no array by its declaration:
its declared type is closed and, at the path, declares keys and no array. */
function declaredNoArray(r: { root: string; path: string[] }, at: ts.Node): boolean {
  const d = declOf(r.root, at);
  if (d === null || d.kind === "function") return false;
  const acc = accOf(d.type, typeDecls(at.getSourceFile()));
  const e = acc.paths.get(r.path.join("."));
  return d.type !== undefined && !acc.open && e !== undefined && !e.array;
}
const isArrayLiteral = (e: ts.Expression | undefined): boolean => e !== undefined && ts.isArrayLiteralExpression(unwrapExpr(e));

function closureEffect(fn: FnNode, paramRoots: boolean = false, skip: Skip = noSkip): Effect | string {
  if (fn.body === undefined) return "has no body";
  const entries: [string, Change][] = [];
  let otherwise: Change = "keep";
  let error: string | null = null;
  const fail = (n: ts.Node, why: string): undefined => { error ??= `the callback's ${n.getText()} ${why}`; return undefined; };
  const keyOf = (r: { root: string; path: string[] }, tail: string): string => [r.root, ...r.path].join(".") + tail;
  const write = (target: ts.Expression, change: Change, at: ts.Node): undefined => {
    const t = unwrapExpr(target);
    if (ts.isPropertyAccessExpression(t) || ts.isElementAccessExpression(t)) {
      const base = resolve_(t.expression, fn, 0, paramRoots);
      if (base === null) return fail(at, "writes a location no key of the instance can name");
      if (base.fresh) return undefined;
      // A key written as a string literal (`x["f"]`) names the field `f`.
      const arg = ts.isElementAccessExpression(t) ? unwrapExpr(t.argumentExpression) : undefined;
      const name = ts.isPropertyAccessExpression(t) ? t.name.text
        : arg !== undefined && (ts.isStringLiteral(arg) || ts.isNoSubstitutionTemplateLiteral(arg)) ? arg.text : null;
      if (name === null) { entries.push([keyOf(base, "[*]"), "grow"], [keyOf(base, "[#]"), "any"]); return undefined; }
      // Field-Write is a rule for a field of an object; a named member of an
      // array (its `length`, which is its spine) is a step no rule gives an
      // effect, and so is a write of `length` where the object is not
      // declared to be no array.
      if (isArrayAt(base, at)) return fail(at, "writes a named member of an array, a step no rule gives an effect");
      if (name === "length" && !declaredNoArray(base, at)) return fail(at, "writes the length of a value not declared to be no array, a step no rule gives an effect");
      entries.push([keyOf(base, "." + name), change]);
      return undefined;
    }
    if (ts.isIdentifier(t)) {
      const d = declOf(t.text, t);
      const local = d !== null && d.kind !== "function" &&
        (d.kind === "param" ? d.owner === fn || within(d.owner, fn) : within(d.at, fn));
      return local ? undefined : fail(at, "assigns a captured binding");
    }
    return fail(at, "writes a location no key of the instance can name");
  };
  const visit = (n: ts.Node): undefined => {
    if (error !== null) return undefined;
    if (n !== fn && isFn(n)) return undefined;
    if (ts.isBinaryExpression(n) && n.operatorToken.kind >= ts.SyntaxKind.FirstAssignment &&
        n.operatorToken.kind <= ts.SyntaxKind.LastAssignment)
      write(n.left, arithmetic.has(n.operatorToken.kind) ? "scalar" : "any", n);
    else if ((ts.isPrefixUnaryExpression(n) || ts.isPostfixUnaryExpression(n)) &&
        (n.operator === ts.SyntaxKind.PlusPlusToken || n.operator === ts.SyntaxKind.MinusMinusToken))
      write(n.operand, "scalar", n);
    else if (ts.isDeleteExpression(n)) write(n.expression, "any", n);
    else if (ts.isNewExpression(n)) {
      // A construction of a library global (`new RangeError(…)`): a fresh
      // object, and the reviewed construct effect of the overlay (rule
      // Native); only an empty one is read here.
      const c = unwrapExpr(n.expression);
      const name = ts.isIdentifier(c) && declOf(c.text, c) === null && importedDecl(c.text, c) === undefined ? c.text : null;
      const entries = name === null ? [] : globalsOverlay.filter((g) => g.global === name && g.member === undefined &&
        (g.constructs === true || g.signature.startsWith("new ")));
      if (entries.length === 0 || !entries.every((g) => g.effect !== undefined && keepsHeap(g.effect)))
        return fail(n, "constructs an object whose reviewed effect may change old storage");
    }
    else if (ts.isCallExpression(n)) {
      const callee = unwrapExpr(n.expression);
      const skipped = ts.isIdentifier(callee) && skip.names.has(callee.text) && (() => {
        const d = declOf(callee.text, callee);
        return d !== null && d.kind === "param" && d.owner === skip.owner;
      })();
      if (ts.isPropertyAccessExpression(callee) && callee.name.text === "push") {
        // Rule Push: `push` of an array, by its declaration; a member named
        // `push` of any other object is an unknown method.
        const base = resolve_(callee.expression, fn, 0, paramRoots);
        if (base === null) return fail(n, "pushes onto an array no key of the instance can name");
        const receiver = unwrapExpr(callee.expression);
        const array = base.fresh
          ? ts.isIdentifier(receiver) && (() => { const d = declOf(receiver.text, receiver); return d !== null && d.kind === "const" && isArrayLiteral(d.init); })()
          : isArrayAt(base, n);
        if (!array) return fail(n, "calls push of a value not declared an array, a method whose effect is not stated");
        if (!base.fresh) entries.push([keyOf(base, "[*]"), "extend"]);
      } else if (skipped) {
        // A call of a bounded callback parameter: its effect is the effect
        // variable's, which the caller's instance gives.
      } else if (ts.isIdentifier(callee)) {
        const d = declOf(callee.text, callee);
        const decl = d?.kind === "function" ? d.node : d === null ? importedDecl(callee.text, callee) : undefined;
        const result = decl?.type;
        const stated = result && ts.isTypeReferenceNode(result) && ts.isIdentifier(result.typeName) &&
          result.typeName.text === "Modifies" ? result.typeArguments?.[0] : undefined;
        // A call of a function with effect parameters whose instances are the
        // calling function's own effect parameters (a forwarding call): its
        // effect is its own effect besides them, read from its body, and the
        // forwarded variables, which the calling function's bound accounts for.
        const outer = effectVars(fn);
        const positions = decl === undefined ? [] : (decl.typeParameters ?? []).flatMap((tp, i) => effectVars(decl).includes(tp.name.text) ? [i] : []);
        const forwards = decl !== undefined && stated === undefined && positions.length > 0 &&
          positions.every((i) => { const t = n.typeArguments?.[i]; return t !== undefined && ts.isTypeReferenceNode(t) && ts.isIdentifier(t.typeName) && outer.includes(t.typeName.text); });
        const eff = stated ? effectOf(stated)
          : forwards && decl !== undefined && !reading.has(decl) ? (() => {
            reading.add(decl);
            const e = closureEffect(decl, true, { owner: decl, names: boundedParams(decl) });
            reading.delete(decl);
            return typeof e === "string" ? null : e;
          })() : null;
        if (decl === undefined || eff === null) return fail(n, "calls a function whose effect is not stated");
        const params = decl.parameters.map((q) => ts.isIdentifier(q.name) ? q.name.text : "");
        for (const [k, c] of eff.entries) {
          const at = params.indexOf(rootOf(k));
          const arg = n.arguments[at];
          const base = arg === undefined ? null : resolve_(arg, fn, 0, paramRoots);
          if (base === null) return fail(n, `passes to ${rootOf(k)} a value no key of the instance can name`);
          // A fresh object's own fields and spine are no change of older
          // storage; a location through one of its fields may be.
          const own = /^(?:\.[A-Za-z_$][\w$]*|\.\*|\[\*\]|\[#\])$/.test(restOf(k));
          if (base.fresh && !own) return fail(n, `passes to ${rootOf(k)} a fresh object whose held storage ${k} may change`);
          if (!base.fresh) entries.push([keyOf(base, restOf(k)), c]);
        }
        if (!le(eff.else, otherwise)) otherwise = eff.else;
      } else if (ts.isPropertyAccessExpression(callee) && ts.isIdentifier(callee.expression) &&
          declOf(callee.expression.text, callee) === null && importedDecl(callee.expression.text, callee) === undefined) {
        // A member of a library global (`Math.max`): its effect is the
        // reviewed one of the library-globals overlay (rule Native); a
        // member whose reviewed effect keeps the heap changes nothing.
        const global = callee.expression.text;
        const member = callee.name.text;
        const entries = globalsOverlay.filter((g) => g.global === global && g.member === member);
        if (entries.length === 0 || !entries.every((g) => g.effect !== undefined && keepsHeap(g.effect)))
          return fail(n, "calls a library member whose reviewed effect may change old storage");
      } else return fail(n, "calls a method whose effect is not stated");
    }
    n.forEachChild(visit);
    return undefined;
  };
  // A parameter's default is a step of the function, evaluated at its call.
  for (const p of fn.parameters) visit(p);
  visit(fn.body);
  return error ?? { entries, else: otherwise };
}

/** The access paths of an effect's reach entry, open where not read. */
const accAt = (e: Effect, key: string): Acc => accFromJson(e.reach?.[key]);

/** Whether a claim's location covers an effect's location: the same
 * location, a field among the fields `x.*`, or a location in the reach
 * `x.**` at an access path of its type. */
function covers(c: Loc, r: Loc, acc: Acc): boolean {
  if (c.kind === "reach") return inside(r, c, acc);
  if (c.kind === "fields") return r.kind === "field" && pathText(r) === pathText(c);
  return r.kind === c.kind && r.key === c.key && pathText(r) === pathText(c);
}

/** **The argument's type at Inst**: the closure's effect is included in the
 * written instance by the paper's order, each entry of the effect within a
 * claim entry covering it (an instance's `else` is `keep`). */
function effectWithin(eff: Effect, claim: Effect): string | null {
  for (const [k, c] of eff.entries) {
    const r = locOf(k);
    if (!r) return `the callback changes ${k}, which no key of the instance can name`;
    const ok = claim.entries.some(([ck, d]) => {
      const l = locOf(ck);
      return l !== null && covers(l, r, accAt(claim, ck)) && le(c, d);
    }) || le(c, claim.else);
    if (!ok) return `the callback changes ${k} by ${c}; the instance allows ${claim.entries.map(([ck, d]) => `${ck}: ${d}`).join(", ") || "nothing"}${claim.else === "keep" ? "" : `, else ${claim.else}`}`;
  }
  return le(eff.else, claim.else) ? null : `the callback's else ${eff.else} exceeds the instance's else ${claim.else}`;
}

/** **Rule Inst**, the paper's order (Definition "Order"): the instance is
 * included in the bound at the actual arguments when, for every bound entry
 * `b : d`, every instance entry not disjoint from `b` is within `d`, and,
 * where the bound's `else` is not `any`, every instance entry lying in no
 * bound entry, and the instance's `else`, are within that `else`. The
 * arguments are paths with their `const` aliases resolved (null for any
 * other expression); `fresh` holds the instance's roots the caller
 * allocated, and `params` the caller's parameters it never assigns. A key
 * this check cannot parse is refused. */
function instCheck(instance: Effect, bound: Effect, params: string[], args: (string | null)[], fresh: Set<string>,
    callerParams: Set<string>): string | null {
  // The empty effect is within every bound, whatever its arguments.
  if (instance.entries.length === 0 && instance.else === "keep") return null;
  const actual = (key: string): string | null => {
    const at = params.indexOf(rootOf(key));
    if (at < 0) return key;
    const arg = args[at];
    return arg === null || arg === undefined ? null : arg + restOf(key);
  };
  const bs: [Loc, Change, string, Acc][] = [];
  for (const [b, d] of bound.entries) {
    const text = actual(b);
    const l = text === null ? null : locOf(text);
    if (text === null || l === null) return `the bound's entry ${b} is not read at this call's arguments`;
    bs.push([l, d, text, accAt(bound, b)]);
  }
  const is: [Loc, Change, Acc, string][] = [];
  for (const [r, c] of instance.entries) {
    const l = locOf(r);
    if (!l) return `the instance's key ${r} is not decided`;
    is.push([l, c, accAt(instance, r), r]);
  }
  for (const [l, c, iacc, r] of is) {
    for (const [b, d, text, bacc] of bs)
      if (!disjoint(l, b, l.kind === "reach" ? iacc : bacc, fresh, callerParams) && !le(c, d))
        return `the instance changes ${r} by ${c}; the bound allows ${text}: ${d}`;
    if (bound.else !== "any" && !bs.some(([b, , , bacc]) => inside(l, b, bacc)) && !le(c, bound.else))
      return `the instance changes ${r} by ${c}; the bound's else allows ${bound.else}`;
  }
  // The instance's `else` reaches the locations of a bound entry that no
  // instance entry covers: the same location, or one inside an instance
  // reach.
  const covered = (b: Loc): boolean => is.some(([l, , iacc]) =>
    l.kind === b.kind && l.key === b.key && pathText(l) === pathText(b) || inside(b, l, iacc));
  for (const [b, d, text] of bs)
    if (!covered(b) && !le(instance.else, d)) return `the instance's else ${instance.else} exceeds the bound's ${text}: ${d}`;
  if (!le(instance.else, bound.else)) return `the instance's else ${instance.else} exceeds the bound's else ${bound.else}`;
  return null;
}

/** Whether an instance is anchored as the prototype decides it
(Definition "Instances and anchoring"): its `else` is `keep`, it has no
class key, and each key is a field, the fields or the spine of a variable
that is a `const` or a parameter its function never assigns; the reason
otherwise. A path through a field, a reach or the cells are anchored only
where their contracts admit one value or no growth, which this script
does not read. */
function anchored(instance: Effect, at: ts.Node): string | null {
  if (instance.classes) return "an instance has no class key (values, spines): such regions are not anchored";
  if (instance.else !== "keep") return `an instance's else is keep; this one's is ${instance.else}, which changes storage allocated after the call`;
  for (const [k] of instance.entries) {
    const l = locOf(k);
    if (l === null || l.path.length > 0 || !(l.kind === "field" || l.kind === "fields" || l.kind === "spine"))
      return `the instance's key ${k} is not a field, the fields or the spine of a variable, which the prototype decides anchored`;
    const d = declOf(l.root, at);
    const rigid = d !== null && (d.kind === "const" || (d.kind === "param" && !assignedIn(l.root, d.owner)));
    if (!rigid) return `the instance's key ${k} is rooted at ${l.root}, which is no const or unassigned parameter`;
  }
  return null;
}

/** The effect variable a callback parameter's type gives its calls, null
where the type mentions no effect variable, or the reason the prototype
does not read it. Read is a function type, a local alias of one, or a union
of one with `undefined` or `null`, whose effect is the variable alone: its
result `Modifies<E, T>`, or a result with no `Modifies` and the variable
only as a phantom (a parameter of type `E`, or an alias's type argument its
function type uses no otherwise). A result `Modifies<[E, P], T>` makes the
callback's effect `ε ∪ P`; the layer reads `ε` alone at the callback's
calls, so a non-empty `P` is refused. */
function callbackVar(type: ts.TypeNode, vars: string[], decls: Map<string, ts.Node>): { variable: string } | string | null {
  const seen = new Set<string>();
  mentions(type, seen);
  const used = vars.filter((v) => seen.has(v));
  if (used.length === 0) return null;
  const isVar = (t: ts.TypeNode, v: string): boolean => ts.isTypeReferenceNode(t) && ts.isIdentifier(t.typeName) &&
    t.typeName.text === v && (t.typeArguments ?? []).length === 0;
  const mentionsName = (t: ts.Node, v: string): boolean => { const m = new Set<string>(); mentions(t, m); return m.has(v); };
  /** A function type whose effect is the variable `x` alone. */
  const arrow = (f: ts.FunctionTypeNode, x: string): string | null => {
    for (const p of f.parameters)
      if (p.type !== undefined && mentionsName(p.type, x) && !isVar(p.type, x))
        return `the callback type uses its effect variable in the parameter ${p.name.getText()}`;
    const r = f.type;
    if (r === undefined) return "the callback type has no result type";
    if (ts.isTypeReferenceNode(r) && ts.isIdentifier(r.typeName) && r.typeName.text === "Modifies") {
      const [eff, result] = r.typeArguments ?? [];
      if (eff === undefined || (result !== undefined && mentionsName(result, x))) return "the callback type's Modifies is not read";
      if (isVar(eff, x)) return null;
      if (ts.isTupleTypeNode(eff) && eff.elements.length === 2 && eff.elements[0] !== undefined && isVar(eff.elements[0], x)) {
        const p = eff.elements[1] === undefined ? null : effectOf(eff.elements[1]);
        if (p !== null && p.entries.length === 0 && p.else === "keep" && !p.classes) return null;
        return `the callback's effect is ${x} with ${eff.elements[1]?.getText() ?? "?"}, which the layer does not read at its calls`;
      }
      return "the callback's stated effect is not its effect variable";
    }
    return mentionsName(r, x) ? "the callback type's result mentions its effect variable" : null;
  };
  const members = ts.isUnionTypeNode(type)
    ? type.types.filter((t) => t.kind !== ts.SyntaxKind.UndefinedKeyword && !(ts.isLiteralTypeNode(t) && t.literal.kind === ts.SyntaxKind.NullKeyword))
    : [type];
  const only = members.length === 1 ? members[0] : undefined;
  const f = only !== undefined && ts.isParenthesizedTypeNode(only) ? only.type : only;
  if (used.length !== 1 || f === undefined) return "a callback type uses one effect variable, in one function type";
  const v = used[0] ?? "";
  if (ts.isFunctionTypeNode(f)) { const why = arrow(f, v); return why ?? { variable: v }; }
  if (ts.isTypeReferenceNode(f) && ts.isIdentifier(f.typeName)) {
    const decl = decls.get(f.typeName.text);
    const args = f.typeArguments ?? [];
    const at = args.findIndex((t) => isVar(t, v));
    if (decl === undefined || !ts.isTypeAliasDeclaration(decl) || !ts.isFunctionTypeNode(decl.type) || at < 0 ||
        args.some((t, i) => i !== at && mentionsName(t, v)))
      return `the callback type ${f.getText()} is no local alias of a function type taking ${v}`;
    const x = decl.typeParameters?.[at]?.name.text;
    if (x === undefined) return `the callback type ${f.getText()} is not read`;
    const why = arrow(decl.type, x);
    return why ?? { variable: v };
  }
  return `the callback type ${f.getText()} is not read`;
}

/** A file's functions with their effect parameters, its function bodies and
 * its type declarations. A function with a bound whose reach its own steps
 * may change, or whose callback's type is not read, is refused
 * (`refusal`). */
function functionInfos(tree: ts.SourceFile): { functions: Record<string, FunctionInfo>; bodies: Map<string, ts.Node>; decls: Map<string, ts.Node> } {
  const functions: Record<string, FunctionInfo> = {};
  const bodies = new Map<string, ts.Node>();
  const decls = new Map<string, ts.Node>();
  for (const s of tree.statements)
    if ((ts.isTypeAliasDeclaration(s) || ts.isInterfaceDeclaration(s))) decls.set(s.name.text, s);
  for (const s of tree.statements) {
    if (!ts.isFunctionDeclaration(s) || !s.name || !s.body) continue;
    bodies.set(s.name.text, s.body);
    const effectParams: EffectParam[] = [];
    let unread: string | undefined;
    for (const tp of s.typeParameters ?? []) {
      const c = tp.constraint;
      if (c && ts.isTypeReferenceNode(c) && ts.isIdentifier(c.typeName) && c.typeName.text === "AtMost") {
        const arg = c.typeArguments?.[0];
        const bound = arg ? effectOf(arg) : null;
        // A bound not read leaves its variable's callbacks unbounded; a class
        // key's region (every value, every spine) is not read in a bound.
        if (bound === null) unread ??= `the bound of ${tp.name.text} is not read`;
        else if (bound.classes) unread ??= `the bound of ${tp.name.text} has a class key (values, spines), which the prototype does not read in a bound`;
        else effectParams.push({ name: tp.name.text, bound });
      }
    }
    const params = s.parameters.map((p) => ts.isIdentifier(p.name) ? p.name.text : "");
    for (const e of effectParams) {
      const reach: Record<string, AccJson> = {};
      for (const [k] of e.bound.entries) {
        const l = locOf(k);
        if (l?.kind !== "reach") continue;
        const p = l.path.length === 0 ? s.parameters[params.indexOf(l.root)] : undefined;
        reach[k] = accJson(accOf(p?.type, decls));
      }
      if (Object.keys(reach).length > 0) e.bound.reach = reach;
    }
    const bounded: FunctionInfo["bounded"] = [];
    s.parameters.forEach((p, index) => {
      const form = p.type === undefined ? null : callbackVar(p.type, effectVars(s), decls);
      if (typeof form === "string") unread ??= `${params[index] ?? ""}: ${form}`;
      else if (form !== null && effectParams.some((e) => e.name === form.variable))
        bounded.push({ param: params[index] ?? "", index, variable: form.variable });
    });
    let refusal = unread;
    const own = effectVars(s).length === 0 ? undefined : closureEffect(s, true, { owner: s, names: boundedParams(s) });
    // Rule Bound's second premise: the regions of each bound read at a
    // callback's call are those read at the function's entry. A field or
    // the spine of a parameter is one location at every state. A reach is
    // read through the fields and spines it holds, so it is read the same
    // where every step since the entry keeps it: the function's own steps
    // (its callbacks' calls keep it by the rule itself).
    if (own !== undefined && refusal === undefined)
      for (const e of effectParams) {
        const reach = e.bound.entries.filter(([k]) => locOf(k)?.kind === "reach");
        if (reach.length === 0) continue;
        const keeps: Effect = { entries: reach.map(([k]) => [k, "keep"]), else: "any" };
        if (e.bound.reach !== undefined) keeps.reach = e.bound.reach;
        const why = typeof own === "string" ? `its own effect is not read (${own})`
          : instCheck(own, keeps, params, params, new Set(), new Set());
        if (why !== null) { refusal = `rule Bound's second premise for ${e.name}: ${why}`; break; }
      }
    const info: FunctionInfo = { typeParams: (s.typeParameters ?? []).map((tp) => tp.name.text), params, effectParams, bounded };
    if (own !== undefined) info.own = own;
    if (refusal !== undefined) info.refusal = refusal;
    if (unread !== undefined) info.unread = unread;
    functions[s.name.text] = info;
  }
  return { functions, bodies, decls };
}

/** The file a relative import names: `./m.js` and `./m` read `./m.ts`. */
function importedFile(from: string, spec: string): string | null {
  if (!spec.startsWith(".")) return null;
  return resolve(dirname(from), spec.replace(/\.(?:js|ts)$/, "") + ".ts");
}

/** The source files of a source's project: every `.ts` file, declaration
files aside, under the nearest directory holding a `tsconfig.json`, outside
`node_modules`. */
function projectFiles(file: string): string[] {
  let root = dirname(file);
  for (let d = root; ; d = dirname(d)) {
    if (existsSync(join(d, "tsconfig.json"))) { root = d; break; }
    if (dirname(d) === d) break;
  }
  const out: string[] = [];
  const walk = (dir: string): void => {
    for (const e of readdirSync(dir, { withFileTypes: true })) {
      if (e.name === "node_modules" || e.name.startsWith(".")) continue;
      const full = join(dir, e.name);
      if (e.isDirectory()) walk(full);
      else if (e.name.endsWith(".ts") && !e.name.endsWith(".d.ts")) out.push(full);
    }
  };
  walk(root);
  return out;
}

/** The function declaration a module's export of a name stands for: a
top-level function of that name, or what an `export … from`, an
`export *` or a local `export { … }` of an imported name re-exports;
null where none is found. */
function exportedFrom(file: string, name: string, depth: number = 0): { file: string; name: string } | null {
  if (depth > 16 || !existsSync(file)) return null;
  const t = treeOf(file);
  for (const st of t.statements)
    if (ts.isFunctionDeclaration(st) && st.name?.text === name && st.body) return { file, name };
  for (const st of t.statements) {
    if (!ts.isExportDeclaration(st) || st.isTypeOnly) continue;
    const spec = st.moduleSpecifier;
    const target = spec !== undefined && ts.isStringLiteral(spec) ? importedFile(file, spec.text) : null;
    if (spec !== undefined && target === null) continue;
    if (st.exportClause === undefined) {
      const r = target === null ? null : exportedFrom(target, name, depth + 1);
      if (r !== null) return r;
      continue;
    }
    if (!ts.isNamedExports(st.exportClause)) continue;
    for (const e of st.exportClause.elements) {
      if (e.isTypeOnly || e.name.text !== name) continue;
      const local = e.propertyName?.getText() ?? e.name.text;
      if (target !== null) return exportedFrom(target, local, depth + 1);
      for (const im of t.statements) {
        if (!ts.isImportDeclaration(im) || !ts.isStringLiteral(im.moduleSpecifier)) continue;
        const named = im.importClause?.namedBindings;
        const from = importedFile(file, im.moduleSpecifier.text);
        if (from === null || !named || !ts.isNamedImports(named)) continue;
        for (const ie of named.elements)
          if (!ie.isTypeOnly && ie.name.text === local) return exportedFrom(from, ie.propertyName?.getText() ?? local, depth + 1);
      }
    }
  }
  return null;
}

/** A file's tree, parsed once. */
function treeOf(file: string): ts.SourceFile {
  let tree = importedFiles.get(file);
  if (tree === undefined) { tree = openText(file, readFileSync(file, "utf8")); importedFiles.set(file, tree); }
  return tree;
}

/** Whether an identifier is in an expression's position: no declaration's
name, import or export specifier, member name, or part of a type. */
function isValueReference(n: ts.Identifier): boolean {
  const p = n.parent;
  if (p === undefined) return false;
  if ((ts.isFunctionDeclaration(p) || ts.isVariableDeclaration(p) || ts.isParameterDeclaration(p)) && p.name === n) return false;
  if (ts.isImportSpecifier(p) || ts.isImportClause(p) || ts.isNamespaceImport(p) || ts.isExportSpecifier(p)) return false;
  if ((ts.isPropertyAccessExpression(p) && p.name === n) || (ts.isPropertyAssignment(p) && p.name === n)) return false;
  for (let m: ts.Node | undefined = p; m; m = m.parent) if (ts.isTypeNode(m)) return false;
  return true;
}

/** The references of a file to quantified functions (`names`: the local
name and the function's own name) that no unit's verdict carries a check
of rule Inst for: a reference other than a call's callee (an alias, an
argument, an export of the value), or a call outside every function
declaration (in a module statement, a class, a `const` closure at the top
level). `bound` tells whether a local name is the quantified function
itself (a local of that name shadows it). */
function uncheckedReferences(tree: ts.SourceFile, names: Map<string, string>, bound: (n: ts.Identifier) => boolean): { name: string; reason: string }[] {
  const out: { name: string; reason: string }[] = [];
  const visit = (n: ts.Node): undefined => {
    if (ts.isIdentifier(n)) {
      const name = names.get(n.text);
      if (name !== undefined && isValueReference(n) && bound(n)) {
        const line = tree.getLineAndCharacterOfPosition(n.getStart()).line + 1;
        const where = `${tree.fileName.split("/").pop() ?? ""}:${line}`;
        const p = n.parent;
        if (p === undefined || !ts.isCallExpression(p) || p.expression !== n)
          out.push({ name, reason: `the reference to ${name} at ${where} is no call, so the calls made through it are not checked against its bounds (a signature holds for every call)` });
        else if (unitOf(n) === null)
          out.push({ name, reason: `the call of ${name} at ${where} is in no function declaration, so no verdict carries its check of rule Inst (a signature holds for every call)` });
      }
    }
    n.forEachChild(visit);
    return undefined;
  };
  visit(tree);
  return out;
}

export function annotations(path: string): {
  functions: Record<string, FunctionInfo>; calls: CallInfo[]; assumes: AssumeInfo[]; refusals: { unit: string; reason: string }[];
} {
  const tree = treeOf(path);
  const { functions, decls } = functionInfos(tree);
  // A callee imported by name from a relative module, directly or through
  // re-exports: its effect parameters are read from the module declaring
  // it, so a call to it is checked as a local one is.
  const imported = new Map<string, { file: string; name: string }>();
  for (const s of tree.statements)
    if (ts.isImportDeclaration(s) && ts.isStringLiteral(s.moduleSpecifier)) {
      const file = importedFile(path, s.moduleSpecifier.text);
      const named = s.importClause?.namedBindings;
      if (file !== null && named && ts.isNamedImports(named))
        for (const e of named.elements)
          if (!e.isTypeOnly) imported.set(e.name.text, { file, name: e.propertyName?.getText() ?? e.name.text });
    }
  const loaded = new Map<string, Record<string, FunctionInfo>>();
  const calleeOf = (name: string, at: ts.Node): FunctionInfo | undefined => {
    const d = declOf(name, at);
    if (d !== null) return d.kind === "function" && d.node.parent !== undefined && ts.isSourceFile(d.node.parent) ? functions[name] : undefined;
    const imp = imported.get(name);
    const found = imp === undefined ? null : exportedFrom(imp.file, imp.name);
    if (found === null) return undefined;
    let fs = loaded.get(found.file);
    if (fs === undefined) {
      fs = functionInfos(treeOf(found.file)).functions;
      loaded.set(found.file, fs);
    }
    return fs[found.name];
  };
  const calls: CallInfo[] = [];
  const assumes: AssumeInfo[] = [];
  const refusals: { unit: string; reason: string }[] = [];
  for (const [name, f] of Object.entries(functions)) if (f.refusal !== undefined) refusals.push({ unit: name, reason: f.refusal });
  // Every reference to this file's quantified functions, here and in the
  // files of its project that import them, directly or through re-exports,
  // is a call some unit checks.
  const quantified = new Map(Object.entries(functions).filter(([, f]) => f.effectParams.length > 0 || f.unread !== undefined)
    .map(([n]) => [n, n]));
  const isLocal = (n: ts.Identifier): boolean => {
    const d = declOf(n.text, n);
    return d !== null && d.kind === "function" && d.node.parent !== undefined && ts.isSourceFile(d.node.parent);
  };
  const unchecked = uncheckedReferences(tree, quantified, isLocal);
  const self = resolve(path);
  const project = projectFiles(self).filter((f) => f !== self);
  // The modules that export something of this file: it, and every module
  // re-exporting from one of them.
  const exporting = new Set([self]);
  for (let grew = true; grew;) {
    grew = false;
    for (const other of project) {
      if (exporting.has(other)) continue;
      const reexports = treeOf(other).statements.some((st) => {
        const spec = ts.isExportDeclaration(st) ? st.moduleSpecifier
          : ts.isImportDeclaration(st) && st.moduleSpecifier !== undefined ? st.moduleSpecifier : undefined;
        if (spec === undefined || !ts.isStringLiteral(spec) || !exporting.has(importedFile(other, spec.text) ?? "")) return false;
        return ts.isExportDeclaration(st) || treeOf(other).statements.some((x) => ts.isExportDeclaration(x) && x.moduleSpecifier === undefined);
      });
      if (reexports) { exporting.add(other); grew = true; }
    }
  }
  if (quantified.size > 0)
    for (const other of project) {
      const t = treeOf(other);
      const f = other.slice(dirname(self).length + 1);
      const names = new Map<string, string>();
      for (const st of t.statements) {
        const spec = ts.isImportDeclaration(st) || ts.isExportDeclaration(st) ? st.moduleSpecifier : undefined;
        if (spec === undefined || !ts.isStringLiteral(spec)) continue;
        const target = importedFile(other, spec.text);
        if (target === null || !exporting.has(target)) continue;
        const clause = ts.isImportDeclaration(st) ? st.importClause?.namedBindings : ts.isExportDeclaration(st) ? st.exportClause : undefined;
        if (clause !== undefined && (ts.isNamespaceImport(clause) || ts.isNamespaceExport(clause)))
          for (const q of quantified.keys()) unchecked.push({ name: q, reason: `${f} names a module exporting ${q} as a namespace, whose calls the prototype does not check` });
        if (ts.isImportDeclaration(st) && clause !== undefined && ts.isNamedImports(clause))
          for (const e of clause.elements) {
            const found = e.isTypeOnly ? null : exportedFrom(target, e.propertyName?.getText() ?? e.name.text);
            if (found !== null && found.file === self && quantified.has(found.name)) names.set(e.name.text, found.name);
          }
      }
      if (names.size > 0) unchecked.push(...uncheckedReferences(t, names, (n) => declOf(n.text, n) === null));
    }
  for (const u of unchecked) refusals.push({ unit: u.name, reason: u.reason });

  const visit = (n: ts.Node): undefined => {
    const unit = unitOf(n);
    const caller = unit?.name?.text;
    if (caller !== undefined && unit !== null && ts.isCallExpression(n) && ts.isIdentifier(n.expression) && n.expression.text === "paperAssume") {
      const form = assumeForm(n);
      const line = tree.getLineAndCharacterOfPosition(n.getStart()).line + 1;
      const fact = n.arguments[0] ?? n;
      assumes.push({ caller, span: [fact.getStart(), fact.getEnd()], line,
        issue: typeof form === "string" ? "" : form.issue,
        ok: typeof form !== "string", reason: typeof form === "string" ? form : null });
    }
    if (caller !== undefined && unit !== null && ts.isCallExpression(n) && ts.isIdentifier(n.expression)) {
      const callee = calleeOf(n.expression.text, n.expression);
      if (callee && callee.unread !== undefined)
        calls.push({ caller, callee: n.expression.text, instance: {}, ok: false,
          reason: `${n.expression.text}'s signature is not read (${callee.unread}), so its calls' effects are not bounded`,
          params: callee.params, bounds: [], own: callee.own ?? "has no effect parameters", span: [n.getStart(), n.getEnd()] });
      else if (callee && callee.effectParams.length > 0) {
        // The instance of each effect parameter: an effect written as the
        // call's type argument; the calling function's own effect parameter
        // (a forwarding call, θ(ε') = ε), whose bound stands for it; or,
        // where every callback the parameter bounds receives `undefined` or
        // is omitted, the empty effect, since no callback runs.
        const outer = functions[caller];
        const instance: Record<string, Effect> = {};
        const forwarded = new Map<string, string>();
        const empty = new Set<string>();
        let reason: string | null = null;
        callee.effectParams.forEach((e) => {
          const arg = n.typeArguments?.[callee.typeParams.indexOf(e.name)];
          const eff = arg ? effectOf(arg) : null;
          const variable = arg !== undefined && ts.isTypeReferenceNode(arg) && ts.isIdentifier(arg.typeName)
            ? outer?.effectParams.find((o) => o.name === arg.typeName.getText()) : undefined;
          const none = callee.bounded.filter((b) => b.variable === e.name).every((b) => {
            const a = n.arguments[b.index];
            return a === undefined || unwrapExpr(a).kind === ts.SyntaxKind.UndefinedKeyword ||
              ts.isIdentifier(unwrapExpr(a)) && unwrapExpr(a).getText() === "undefined";
          });
          if (eff) {
            instance[e.name] = eff;
            reason ??= anchored(eff, n);
          } else if (variable) { instance[e.name] = variable.bound; forwarded.set(e.name, variable.name); }
          else if (arg === undefined && none) { instance[e.name] = { entries: [], else: "keep" }; empty.add(e.name); }
        });
        const args = n.arguments.map((a) => argPath(a));
        // The caller's parameters it never assigns: their values and own
        // locations are apart from what the caller allocates.
        const callerParams = new Set(unit.parameters.map((q) => ts.isIdentifier(q.name) ? q.name.text : "")
          .filter((q) => q !== "" && !assignedIn(q, unit)));
        for (const e of callee.effectParams) {
          if (reason !== null) break;
          const written = instance[e.name];
          if (written === undefined) { reason = `no instance written for ${e.name}`; break; }
          // The instance's roots resolved at the call: aliases replaced by
          // the paths they hold, and the objects the caller allocated.
          const fresh = new Set<string>();
          const entries: [string, Change][] = [];
          const reach: Record<string, AccJson> = {};
          for (const [k, c] of written.entries) {
            const norm = normalizeKey(k, n, unit);
            if (norm === null) { reason = `the instance's key ${k} names no variable of the caller`; break; }
            if (norm.fresh) fresh.add(rootOf(norm.key));
            entries.push([norm.key, c]);
            const a = written.reach?.[k];
            if (a !== undefined) reach[norm.key] = a;
          }
          if (reason !== null) break;
          const inst: Effect = Object.keys(reach).length > 0 ? { entries, else: written.else, reach } : { entries, else: written.else };
          for (const b of callee.bounded.filter((x) => x.variable === e.name)) {
            if (empty.has(e.name)) break;
            let arg: ts.Expression | undefined = n.arguments[b.index];
            // A forwarded variable: the callback is one of the calling
            // function's own callbacks of that variable, or a closure whose
            // only effect on old storage is calls of them (effect ε) besides
            // fresh allocations.
            const outerVar = forwarded.get(e.name);
            if (outerVar !== undefined) {
              const own = new Set((outer?.bounded ?? []).filter((o) => o.variable === outerVar).map((o) => o.param));
              const passed = arg === undefined ? undefined : unwrapExpr(arg);
              if (passed !== undefined && ts.isIdentifier(passed) && own.has(passed.text) &&
                  declOf(passed.text, passed)?.kind === "param") continue;
              if (passed === undefined || !(ts.isArrowFunction(passed) || ts.isFunctionExpression(passed))) {
                reason = `the callback passed for ${b.param} is neither a callback of ${outerVar} nor a closure`;
                break;
              }
              const eff = closureEffect(passed, false, { owner: unit, names: own });
              reason = typeof eff === "string" ? eff
                : eff.entries.length > 0 || eff.else !== "keep"
                  ? `the callback also changes ${eff.entries.map(([k, c]) => `${k} by ${c}`).join(", ") || `else ${eff.else}`}, which ${e.name} forwarded as ${caller}'s effect variable ${outerVar} does not allow`
                  : null;
              if (reason !== null) break;
              continue;
            }
            if (arg !== undefined && ts.isIdentifier(unwrapExpr(arg))) {
              const d = declOf(unwrapExpr(arg).getText(), arg);
              arg = d !== null && d.kind === "const" ? d.init : undefined;
            }
            const fn = arg === undefined ? undefined : unwrapExpr(arg);
            if (fn === undefined || !(ts.isArrowFunction(fn) || ts.isFunctionExpression(fn))) {
              reason = `the callback passed for ${b.param} has no body visible here`;
              break;
            }
            const eff = closureEffect(fn);
            reason = typeof eff === "string" ? eff : effectWithin(eff, inst);
            if (reason !== null) break;
          }
          if (reason !== null) break;
          reason = instCheck(inst, e.bound, callee.params, args, fresh, callerParams);
        }
        // The call's effect at the caller (Inst's conclusion) is within the
        // bounds and the callee's own effect; an empty instance stands for
        // its bound exactly.
        calls.push({ caller, callee: n.expression.text, instance, ok: reason === null, reason,
          params: callee.params, bounds: callee.effectParams.map((e) => empty.has(e.name) ? instance[e.name] ?? e.bound : e.bound),
          own: callee.own ?? "has no effect parameters", span: [n.getStart(), n.getEnd()] });
      }
    }
    n.forEachChild(visit);
    return undefined;
  };
  visit(tree);
  closeParser();
  importedFiles.clear();
  return { functions, calls, assumes, refusals };
}

if (process.argv[1] && resolve(process.argv[1]) === import.meta.filename) {
  const file = process.argv[2];
  if (file === undefined) {
    process.stderr.write("usage: node dev/paper-annotations.mts file.ts\n");
    process.exitCode = 2;
  } else process.stdout.write(JSON.stringify(annotations(resolve(file)), null, 2) + "\n");
}
