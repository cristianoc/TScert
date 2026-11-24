// ============================================================================
// PROTOTYPE ONLY — SCHEDULED FOR DELETION UPON UNIFICATION
// Disposable experimental paper-rules prototype (`docs/drafts/paper-rules-mode.md`).
// Must NEVER be imported by `tools/`, `pipeline/`, or `lean/Verification/`
// (enforced by `tests/prototype-isolation.mts`). Replaced upon unification by
// mechanical annotation parsing plus proved CFG checks in `lean/Verification/`.
// ============================================================================

// The paper's annotations in a source file, for the experimental prototype of
// docs/drafts/paper-rules-mode.md: each function's effect type parameters
// with their `AtMost<P>` bounds and the parameters whose types mention them,
// and each call that writes an instance of such a parameter, with the check
// of the instance against the bound (rule Inst). The ordinary front end reads
// a bound's and an instance's effect as arguments without type meaning, and a
// callback's `Modifies<E, T>` as changing every location
// (docs/SOURCE-CONTRACTS.md, "Arguments without type meaning").
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
  /** Verified stated `Effects<P, T>` on a monomorphic function (e.g.
   * `Effects<{ "@state": "any" }, T>`), used to frame calls to it via rule
   * Confined. */
  stated?: Effect;
  /** Bounded callback parameters verified never to escape this function's
   * dynamic extent (rule Callback-Inv). */
  nonEscaping?: string[];
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
  params: string[]; bounds: Effect[]; callerParams?: string[]; callerBounds?: Effect[]; own: Effect | string; span: [number, number];
  scopedCallbacks?: { span: [number, number]; paramIndex: number }[];
}

/** An unsafe assume `paperAssume(fact, "#n");`: the condition `fact` states
 * what the sound verifier should have established there, and the issue
 * tracks the verifier's extension. Its form is read here; the prototype
 * checks the statement as `if (!(fact)) throw "#n";`. */
interface AssumeInfo {
  caller: string; issue: string; line: number; ok: boolean; reason: string | null;
}

/** An assume's form: the statement `paperAssume(fact, "#n");`; the reason
 * otherwise. */
function assumeForm(n: ts.CallExpression): { issue: string } | string {
  const [fact, issue] = n.arguments;
  if (fact === undefined || issue === undefined || n.arguments.length !== 2 || !ts.isStringLiteral(issue) ||
      !ts.isExpressionStatement(n.parent))
    return "an assume is the statement paperAssume(fact, \"#issue\");";
  return { issue: issue.text };
}

/** The effect a type writes: the paper's literal as an object type,
 * `{ "x[*]": "keep"; else: "any" }`; null for any other type. */
function effectOf(node: ts.TypeNode): Effect | null {
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
      // A class key bounds every location of its class: the effect read
      // here has no class regions, so it widens the `else` (each location is
      // in one class, and a change on a class the other key names is within
      // the max).
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
key), and a type alias or interface named in the same file or imported from
a relative module. Any other form (a tuple, an index or call signature, a
method, a mapped or conditional type, an external name, a recursive
reference) is open: it may declare any key, so no key is decided absent from
the reach. */
interface Acc { paths: Map<string, { keys: Set<string>; array: boolean }>; open: boolean }

/** A type declaration (alias or interface) exported from a module, directly
or through re-exports. */
function exportedTypeFrom(file: string, name: string, depth: number = 0): { node: ts.Node; file: ts.SourceFile } | null {
  if (depth > 16 || !existsSync(file)) return null;
  const t = treeOf(file);
  for (const st of t.statements)
    if ((ts.isTypeAliasDeclaration(st) || ts.isInterfaceDeclaration(st)) && st.name.text === name)
      return { node: st, file: t };
  for (const st of t.statements) {
    if (!ts.isExportDeclaration(st)) continue;
    const spec = st.moduleSpecifier;
    const target = spec !== undefined && ts.isStringLiteral(spec) ? importedFile(file, spec.text) : null;
    if (spec !== undefined && target === null) continue;
    if (st.exportClause === undefined) {
      const r = target === null ? null : exportedTypeFrom(target, name, depth + 1);
      if (r !== null) return r;
      continue;
    }
    if (!ts.isNamedExports(st.exportClause)) continue;
    for (const e of st.exportClause.elements) {
      if (e.name.text !== name) continue;
      const local = e.propertyName?.getText() ?? e.name.text;
      if (target !== null) return exportedTypeFrom(target, local, depth + 1);
      for (const im of t.statements) {
        if (!ts.isImportDeclaration(im) || !ts.isStringLiteral(im.moduleSpecifier)) continue;
        const named = im.importClause?.namedBindings;
        const from = importedFile(file, im.moduleSpecifier.text);
        if (from === null || !named || !ts.isNamedImports(named)) continue;
        for (const ie of named.elements)
          if (ie.name.text === local) return exportedTypeFrom(from, ie.propertyName?.getText() ?? local, depth + 1);
      }
    }
  }
  return null;
}

/** Resolve a named type alias or interface in `sf` or imported from a relative module. */
function resolveTypeDecl(name: string, sf: ts.SourceFile): { node: ts.Node; file: ts.SourceFile } | null {
  const local = typeDecls(sf).get(name);
  if (local !== undefined) return { node: local, file: sf };
  for (const st of sf.statements) {
    if (!ts.isImportDeclaration(st) || !ts.isStringLiteral(st.moduleSpecifier)) continue;
    const named = st.importClause?.namedBindings;
    if (!named || !ts.isNamedImports(named)) continue;
    const elem = named.elements.find((e) => e.name.text === name);
    if (!elem) continue;
    const target = importedFile(sf.fileName, st.moduleSpecifier.text);
    if (target === null) return null;
    return exportedTypeFrom(target, elem.propertyName?.getText() ?? elem.name.text);
  }
  return null;
}

function accOf(node: ts.TypeNode | undefined, sf: ts.SourceFile): Acc {
  const acc: Acc = { paths: new Map(), open: false };
  const at = (path: string[]): { keys: Set<string>; array: boolean } => {
    const k = path.join(".");
    let e = acc.paths.get(k);
    if (e === undefined) { e = { keys: new Set(), array: false }; acc.paths.set(k, e); }
    return e;
  };
  const members = (ms: ts.NodeArray<ts.TypeElement>, path: string[], seen: string[], curSf: ts.SourceFile): void => {
    at(path);
    for (const m of ms) {
      if (ts.isPropertySignatureDeclaration(m) && (ts.isIdentifier(m.name) || ts.isStringLiteral(m.name))) {
        at(path).keys.add(m.name.text);
        walk(m.type, [...path, m.name.text], seen, curSf);
      } else acc.open = true;
    }
  };
  const named = (name: string, args: ts.NodeArray<ts.TypeNode> | undefined, path: string[], seen: string[], curSf: ts.SourceFile): void => {
    const resolved = resolveTypeDecl(name, curSf);
    if (resolved === null) {
      if (/^(?:Uint8|Uint8Clamped|Int8|Uint16|Int16|Uint32|Int32|Float32|Float64)Array$/.test(name)) { at(path).array = true; return; }
      if ((name === "Array" || name === "ReadonlyArray") && args?.length === 1) {
        at(path).array = true;
        return walk(args[0], [...path, "[*]"], seen, curSf);
      }
      acc.open = true;
      return;
    }
    const key = `${resolved.file.fileName}#${name}`;
    if (seen.includes(key) || (args ?? []).length > 0) { acc.open = true; return; }
    const inner = [...seen, key];
    const decl = resolved.node;
    if (ts.isTypeAliasDeclaration(decl) && (decl.typeParameters ?? []).length === 0) return walk(decl.type, path, inner, resolved.file);
    if (ts.isInterfaceDeclaration(decl) && (decl.typeParameters ?? []).length === 0) {
      for (const h of decl.heritageClauses ?? [])
        for (const t of h.types) {
          if (ts.isIdentifier(t.expression) && (t.typeArguments ?? []).length === 0) named(t.expression.text, undefined, path, inner, resolved.file);
          else acc.open = true;
        }
      return members(decl.members, path, inner, resolved.file);
    }
    acc.open = true;
  };
  const walk = (n: ts.TypeNode | undefined, path: string[], seen: string[], curSf: ts.SourceFile): void => {
    if (n === undefined) { acc.open = true; return; }
    switch (n.kind) {
      case ts.SyntaxKind.NumberKeyword: case ts.SyntaxKind.StringKeyword: case ts.SyntaxKind.BooleanKeyword:
      case ts.SyntaxKind.BigIntKeyword: case ts.SyntaxKind.SymbolKeyword: case ts.SyntaxKind.NullKeyword:
      case ts.SyntaxKind.UndefinedKeyword: case ts.SyntaxKind.VoidKeyword: case ts.SyntaxKind.NeverKeyword:
        return;
    }
    if (ts.isLiteralTypeNode(n)) return;
    if (ts.isParenthesizedTypeNode(n)) return walk(n.type, path, seen, curSf);
    if (ts.isUnionTypeNode(n) || ts.isIntersectionTypeNode(n)) { for (const t of n.types) walk(t, path, seen, curSf); return; }
    if (ts.isArrayTypeNode(n)) { at(path).array = true; return walk(n.elementType, [...path, "[*]"], seen, curSf); }
    if (ts.isTypeOperatorNode(n) && n.operator === ts.SyntaxKind.ReadonlyKeyword && ts.isArrayTypeNode(n.type))
      return walk(n.type, path, seen, curSf);
    if (ts.isTypeLiteralNode(n)) return members(n.members, path, seen, curSf);
    if (ts.isTypeReferenceNode(n) && ts.isIdentifier(n.typeName)) return named(n.typeName.text, n.typeArguments, path, seen, curSf);
    acc.open = true;
  };
  walk(node, [], [], sf);
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
  | { kind: "const" | "let"; init: ts.Expression | undefined; type: ts.TypeNode | undefined; at: ts.Node; field?: string }
  | { kind: "function"; node: ts.FunctionDeclaration };

function declIn(statements: readonly ts.Statement[], name: string): Decl | null {
  for (const st of statements) {
    if (ts.isVariableStatement(st)) {
      const list = st.declarationList;
      const kind = (list.flags & ts.NodeFlags.Const) !== 0 ? "const" : "let";
      for (const d of list.declarations) {
        if (ts.isIdentifier(d.name) && d.name.text === name)
          return { kind, init: d.initializer, type: d.type, at: d };
        if (ts.isObjectBindingPattern(d.name))
          for (const el of d.name.elements) {
            if (el.dotDotDotToken !== undefined || el.initializer !== undefined) continue;
            if (el.name === undefined || !ts.isIdentifier(el.name) || el.name.text !== name) continue;
            const field = el.propertyName === undefined ? name
              : ts.isIdentifier(el.propertyName) ? el.propertyName.text : undefined;
            if (field !== undefined) return { kind, init: d.initializer, type: undefined, at: d, field };
          }
      }
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

/** Whether a function declaration is a pure identity returning its single
 * parameter unchanged: `function f(x) { return x }`. */
function isIdentityFn(decl: ts.FunctionDeclaration): boolean {
  if (decl.parameters.length !== 1 || !decl.body || decl.body.statements.length !== 1) return false;
  const param = decl.parameters[0];
  const stmt = decl.body.statements[0];
  if (!param || !ts.isIdentifier(param.name) || param.initializer || param.dotDotDotToken) return false;
  if (!stmt || !ts.isReturnStatement(stmt) || !stmt.expression) return false;
  const ret = unwrapExpr(stmt.expression);
  return ts.isIdentifier(ret) && ret.text === param.name.text;
}

/** Resolve a call `f(x)` to its argument `x` when `f` is a local or imported
 * pure identity function (`function f(x) { return x }`). */
function unwrapIdentityCall(e: ts.Expression): ts.Expression {
  let cur = unwrapExpr(e);
  for (let steps = 0; steps < 8 && ts.isCallExpression(cur) && cur.arguments.length === 1 && ts.isIdentifier(unwrapExpr(cur.expression)); steps++) {
    const callee = unwrapExpr(cur.expression);
    if (!ts.isIdentifier(callee)) break;
    const d = declOf(callee.text, callee);
    const decl = d?.kind === "function" ? d.node : d === null ? importedDecl(callee.text, callee) : undefined;
    const arg = cur.arguments[0];
    if (decl === undefined || arg === undefined || !isIdentityFn(decl)) break;
    cur = unwrapExpr(arg);
  }
  return cur;
}

const TYPED_ARRAY_NAMES = new Set<string>([
  "Uint8Array", "Uint8ClampedArray", "Int8Array", "Uint16Array", "Int16Array",
  "Uint32Array", "Int32Array", "Float32Array", "Float64Array",
]);

const COLLECTION_NAMES = new Set<string>(["Map", "WeakMap", "Set"]);

const NUMERIC_BINARY_OPS = new Set<ts.SyntaxKind>([
  ts.SyntaxKind.MinusToken, ts.SyntaxKind.AsteriskToken, ts.SyntaxKind.AsteriskAsteriskToken,
  ts.SyntaxKind.SlashToken, ts.SyntaxKind.PercentToken, ts.SyntaxKind.LessThanLessThanToken,
  ts.SyntaxKind.GreaterThanGreaterThanToken, ts.SyntaxKind.GreaterThanGreaterThanGreaterThanToken,
  ts.SyntaxKind.AmpersandToken, ts.SyntaxKind.BarToken, ts.SyntaxKind.CaretToken,
]);

/** Whether an expression is syntactically a numeric expression (guaranteed to
 * pass a length, never an existing ArrayBuffer or view, to `new TypedArray(len)`). */
function isNumericExpr(e: ts.Expression): boolean {
  const u = unwrapExpr(e);
  if (ts.isNumericLiteral(u)) return true;
  if (ts.isPropertyAccessExpression(u) && u.name.text === "length") return true;
  if (ts.isPrefixUnaryExpression(u)) return isNumericExpr(u.operand);
  if (ts.isBinaryExpression(u))
    return NUMERIC_BINARY_OPS.has(u.operatorToken.kind) || (isNumericExpr(u.left) && isNumericExpr(u.right));
  if (ts.isCallExpression(u) && ts.isIdentifier(unwrapExpr(u.expression))) {
    const cname = unwrapExpr(u.expression).getText();
    const d = declOf(cname, u.expression);
    if (d !== null && d.kind === "function" && d.node.type?.kind === ts.SyntaxKind.NumberKeyword) return true;
    if (d !== null && d.kind === "const" && d.init !== undefined && isFn(unwrapExpr(d.init))) {
      const fnNode = unwrapExpr(d.init);
      if (isFn(fnNode) && fnNode.type?.kind === ts.SyntaxKind.NumberKeyword) return true;
    }
  }
  if (ts.isIdentifier(u)) {
    const d = declOf(u.text, u);
    if (d !== null && d.kind !== "function" && d.type !== undefined)
      return d.type.kind === ts.SyntaxKind.NumberKeyword;
    if (d !== null && d.kind === "const" && d.init !== undefined) return isNumericExpr(d.init);
  }
  return false;
}

/** Whether an expression is a fresh empty collection construction
 * (`new Map()`, `new WeakMap()`, `new Set()` with zero arguments). */
function isFreshCollectionAlloc(e: ts.Expression | undefined): boolean {
  if (e === undefined) return false;
  const u = unwrapExpr(e);
  if (!ts.isNewExpression(u) || !ts.isIdentifier(unwrapExpr(u.expression))) return false;
  const name = unwrapExpr(u.expression).getText();
  return COLLECTION_NAMES.has(name) && (u.arguments === undefined || u.arguments.length === 0);
}

/** Whether an expression allocates a fresh typed array with a fresh backing
 * buffer (`new Int32Array(n)` for numeric `n`, optionally `.fill(...)`, never
 * `new Int32Array(buf)` or `a.subarray(...)`). */
function isFreshTypedArrayAlloc(e: ts.Expression | undefined): boolean {
  if (e === undefined) return false;
  const u = unwrapExpr(e);
  if (ts.isCallExpression(u) && ts.isPropertyAccessExpression(unwrapExpr(u.expression)) &&
      unwrapExpr(u.expression).getText().endsWith(".fill")) {
    const p = unwrapExpr(u.expression);
    if (ts.isPropertyAccessExpression(p) && p.name.text === "fill") return isFreshTypedArrayAlloc(p.expression);
  }
  if (!ts.isNewExpression(u)) return false;
  const c = unwrapExpr(u.expression);
  if (!ts.isIdentifier(c) || !TYPED_ARRAY_NAMES.has(c.text)) return false;
  if (u.arguments === undefined || u.arguments.length !== 1) return false;
  const arg = u.arguments[0];
  return arg !== undefined && isNumericExpr(arg);
}

const isAllocation = (e: ts.Expression | undefined): boolean =>
  e !== undefined && (ts.isObjectLiteralExpression(unwrapExpr(e)) || ts.isArrayLiteralExpression(unwrapExpr(e)));

/** Whether an expression freshly allocates a new object, array, empty
 * collection, or fresh-buffer typed array. */
const isFreshContainerAlloc = (e: ts.Expression | undefined): boolean =>
  isAllocation(e) || isFreshCollectionAlloc(e) || isFreshTypedArrayAlloc(e);

/** Whether an expression is a primitive or nullish literal (no heap reference). */
function isPrimitiveLiteral(e: ts.Expression | undefined): boolean {
  if (e === undefined) return true;
  const u = unwrapExpr(e);
  if (u.kind === ts.SyntaxKind.NullKeyword || u.kind === ts.SyntaxKind.TrueKeyword ||
      u.kind === ts.SyntaxKind.FalseKeyword || u.kind === ts.SyntaxKind.UndefinedKeyword) return true;
  if (ts.isIdentifier(u) && u.text === "undefined") return true;
  if (ts.isNumericLiteral(u) || ts.isStringLiteral(u) || ts.isNoSubstitutionTemplateLiteral(u)) return true;
  if (ts.isPrefixUnaryExpression(u) && (u.operator === ts.SyntaxKind.MinusToken || u.operator === ts.SyntaxKind.PlusToken))
    return ts.isNumericLiteral(unwrapExpr(u.operand));
  return false;
}

/** Whether a module-level initializer is fresh (primitive/nullish, fresh empty
 * container, or literal with primitive/fresh members). */
function isFreshModuleInit(e: ts.Expression | undefined): boolean {
  if (isPrimitiveLiteral(e) || isFreshCollectionAlloc(e) || isFreshTypedArrayAlloc(e)) return true;
  if (e === undefined) return true;
  const u = unwrapExpr(e);
  if (ts.isArrayLiteralExpression(u)) return u.elements.every((el) => isFreshModuleInit(el));
  if (ts.isObjectLiteralExpression(u))
    return u.properties.every((p) => ts.isPropertyAssignment(p) && isFreshModuleInit(p.initializer));
  return false;
}

const isPathExpr = (e: ts.Expression | undefined): e is ts.Expression => {
  if (e === undefined) return false;
  const u = unwrapIdentityCall(e);
  return ts.isIdentifier(u) || (ts.isPropertyAccessExpression(u) && isPathExpr(u.expression));
};

function resolve_(expr: ts.Expression, closure: ts.Node | null, depth: number = 0, paramRoots: boolean = false,
    freshLocals?: ReadonlySet<ts.Node>): Resolved | null {
  const e = unwrapIdentityCall(expr);
  if (depth > 32) return null;
  if (ts.isPropertyAccessExpression(e)) {
    const base = resolve_(e.expression, closure, depth + 1, paramRoots, freshLocals);
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
  if (local && freshLocals?.has(d.at)) return { fresh: true };
  if (d.kind === "const" && d.field !== undefined && isPathExpr(d.init)) {
    const base = resolve_(d.init, closure, depth + 1, paramRoots, freshLocals);
    if (base === null || base.fresh) return null;
    return { fresh: false, root: base.root, path: [...base.path, d.field] };
  }
  if (d.kind === "const" && isPathExpr(d.init)) return resolve_(d.init, closure, depth + 1, paramRoots, freshLocals);
  if (local) return d.kind === "const" && isFreshContainerAlloc(d.init) ? { fresh: true } : null;
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

/** The nearest function or class enclosing a node: the code that runs
when it runs. */
function runnerOf(n: ts.Node): ts.Node | null {
  for (let m: ts.Node | undefined = n.parent; m; m = m.parent)
    if (ts.isFunctionLikeDeclaration(m) || ts.isClassDeclaration(m) || ts.isClassExpression(m)) return m;
  return null;
}

/** Whether an object a `const` holds may be reached from other storage when
a call runs: some reference to the binding (or to a `const` alias of it)
other than the object of a member access (`x.f`, `x[i]`, `x.push(…)`),
which may store, pass or return it, can run before the call. Such a
reference precedes the call, lies in the call's arguments, lies in a
function or class nested in the code that runs the call (which may run at
any time), or lies in a loop enclosing the call and not the declaration
(which runs it before a later iteration's call). Where the call itself runs
in other code than the declaration, every such reference counts. */
function escapesBefore(decl: ts.VariableDeclaration, call: ts.Node, scope: ts.Node): boolean {
  if (!ts.isIdentifier(decl.name)) return true;
  const name = decl.name.text;
  const runner = runnerOf(decl);
  const anywhere = runnerOf(call) !== runner;
  const loops: ts.Node[] = [];
  for (let m: ts.Node | undefined = call.parent; m && m !== runner; m = m.parent)
    if ((ts.isForStatement(m) || ts.isForInStatement(m) || ts.isForOfStatement(m) || ts.isWhileStatement(m) ||
        ts.isDoStatement(m)) && !within(decl, m.statement)) loops.push(m);
  const before = (n: ts.Node): boolean => anywhere || n.getStart() < call.getStart() || within(n, call) ||
    runnerOf(n) !== runner || loops.some((l) => within(n, l));
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
        if (alias) { if (escapesBefore(p, call, scope)) out = true; }
        else if (!member && before(n)) out = true;
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
function allocated and no reference lets reach other storage before the
call: a `const` of its body initialised by an object or array literal
(Rule Alloc of Tolerant frames gives its separation from every location
older than it); null where the root resolves to nothing this script
reads. */
function normalizeKey(key: string, call: ts.Node, unit: ts.Node | null): { key: string; fresh: boolean } | null {
  if (key === "@state") return { key: "@state", fresh: false };
  const root = rootOf(key);
  const d = declOf(root, call);
  if (d === null || d.kind === "function") return null;
  if (d.kind === "const" && isPathExpr(d.init)) {
    const inner = d.init === undefined ? null : resolveAt(d.init);
    if (inner === null) return null;
    const head = [inner.root, ...inner.path].join(".");
    const fresh = inner.path.length === 0 && freshAt(inner.root, d.init ?? call, call, unit);
    return { key: head + restOf(key), fresh };
  }
  return { key, fresh: freshAt(root, call, call, unit) };
}

/** Whether a variable, read at a node, holds an object the unit allocated
in its body that no reference able to run before the call lets reach other
storage. */
function freshAt(name: string, at: ts.Node, call: ts.Node, unit: ts.Node | null): boolean {
  const d = declOf(name, at);
  if (unit === null || d === null || d.kind !== "const" || !isAllocation(d.init) || !within(d.at, unit)) return false;
  return ts.isVariableDeclaration(d.at) && !escapesBefore(d.at, call, unit);
}

function resolveAt(e: ts.Expression): { root: string; path: string[] } | null {
  const r = resolve_(e, null);
  return r === null || r.fresh ? null : r;
}

/** A call's argument as a path, its `const` aliases and pure identity calls
resolved; null for any other expression. */
function argPath(e: ts.Expression): string | null {
  if (!isPathExpr(e)) return null;
  const r = resolveAt(e);
  return r === null ? null : [r.root, ...r.path].join(".");
}

/** A region key, parsed: its root, the declared keys from the root to the
location's object, and what it names there: a field, every field (`.*`),
the spine (`[*]`), the cells (`[#]`), the reach through declared keys
(`.**`), or confined module-private state (`@state`). */
interface Loc {
  root: string; path: string[];
  kind: "field" | "fields" | "spine" | "cells" | "reach" | "modState";
  key: string | null;
}

function locOf(key: string): Loc | null {
  if (key === "@state") return { root: "@state", path: [], kind: "modState", key: null };
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

/** Whether reach `sub` (at `subAcc`) is contained in reach `sup` (at `supAcc`):
`sub`'s base path extends `sup`'s base path by `prefix`, and every declared
path, key, and array flag in `subAcc` appears at `prefix ++ path` in `supAcc`. */
function reachInside(sub: Loc, subAcc: Acc, sup: Loc, supAcc: Acc): boolean {
  const base = [sup.root, ...sup.path];
  const full = [sub.root, ...sub.path];
  if (full.length < base.length || base.some((x, i) => full[i] !== x)) return false;
  const prefix = full.slice(base.length);
  if (subAcc.open || supAcc.open) return prefix.length === 0 && subAcc.open === supAcc.open && subAcc.paths.size === 0 && supAcc.paths.size === 0;
  for (const [subPath, subEntry] of subAcc.paths) {
    const steps = subPath === "" ? prefix : [...prefix, ...subPath.split(".")];
    const supEntry = supAcc.paths.get(steps.join("."));
    if (supEntry === undefined) return false;
    if (subEntry.array && !supEntry.array) return false;
    for (const k of subEntry.keys) if (!supEntry.keys.has(k)) return false;
  }
  return true;
}

/** Whether two locations are disjoint, decided from the source
(docs/drafts/effect-languages.md, "Decisions"): confined module-private state
`@state` is disjoint from every external root region (rule Confined,
`Model.closedOut_region_disjoint` / `closedOut_reach_disjoint`); a field
location, a spine and cells differ (their keys differ); two field locations
at different keys differ whatever objects they are on (disjointness by key);
a field whose key no type in a closed reach declares lies outside it; and an
own location (a field or the spine, at the empty path) of an object the
caller allocated is apart from an own location of a parameter the caller
never assigns, and, where no reference lets the object reach other storage
before the call, from the parameter's reach (rule Alloc of Tolerant frames).
Anything else may overlap. `acc` is the reach's access paths where one of
them is a reach. */
function disjoint(r: Loc, b: Loc, acc: Acc, fresh: Set<string>, params: Set<string>): boolean {
  if (r.kind === "modState" || b.kind === "modState") return r.kind !== b.kind;
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

/** Whether `r` lies in `b`: the same location, a reach contained in a reach,
or a location at a path `Acc(T)` admits when `b` is a reach. */
function inside(r: Loc, b: Loc, acc: Acc, racc?: Acc): boolean {
  if (r.kind === "modState" || b.kind === "modState") return r.kind === "modState" && b.kind === "modState";
  if (b.kind === "reach") {
    if (r.kind === "reach") return racc !== undefined && reachInside(r, racc, b, acc);
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
  const acc = accOf(d.type, at.getSourceFile());
  const e = acc.paths.get(r.path.join("."));
  return !acc.open && e !== undefined && e.array && e.keys.size === 0;
}
/** Whether a location expression is declared a closed array of primitives
 * (no object or nested-array element paths in its declared reach). */
function isPrimitiveArrayAt(r: { root: string; path: string[] }, at: ts.Node): boolean {
  const d = declOf(r.root, at);
  if (d === null || d.kind === "function") return false;
  const acc = accOf(d.type, at.getSourceFile());
  const e = acc.paths.get(r.path.join("."));
  return !acc.open && e !== undefined && e.array && e.keys.size === 0 &&
    acc.paths.get([...r.path, "[*]"].join(".")) === undefined;
}
/** Whether a location expression's value is no array by its declaration:
its declared type is closed and, at the path, declares keys and no array. */
function declaredNoArray(r: { root: string; path: string[] }, at: ts.Node): boolean {
  const d = declOf(r.root, at);
  if (d === null || d.kind === "function") return false;
  const acc = accOf(d.type, at.getSourceFile());
  const e = acc.paths.get(r.path.join("."));
  return d.type !== undefined && !acc.open && e !== undefined && !e.array;
}
const isArrayLiteral = (e: ts.Expression | undefined): boolean => e !== undefined && ts.isArrayLiteralExpression(unwrapExpr(e));

/** Local module confinement check (`OwnerConfined`,
 * `docs/drafts/abstract-confined-regions.md` §2):
 *
 * For a module `M`, a top-level binding `b` belongs to `M`'s confined state
 * `M.@state` when it is unexported, initialized with a fresh/primitive value,
 * and satisfies either:
 * - **Cell-only (`let`)**: never mutated through (neither `b.f = …`, `b[i] = …`,
 *   nor mutating methods on `b` or any local alias of `b`); writes to `b` touch
 *   only the unexported module cell `b` (`Role.cell`).
 * - **Interior container (`const`)**: initialized with a fresh container
 *   (`{}`, `[]`, `new Map()`, `new WeakMap()`, `new Set()`, or fresh-buffer
 *   `new TypedArray(len)`), never escapes `M`, and if any value loaded from `b`
 *   (via `b.get(…)` / `b[k]` / `b.f`) is mutated, every value stored into `b`
 *   is freshly allocated and no loaded nested container escapes `M` or has its
 *   own loaded payloads mutated after load. */
interface ConfinedModuleInfo {
  cells: Set<ts.VariableDeclaration>;
  containers: Set<ts.VariableDeclaration>;
  nestedLocals: Set<ts.VariableDeclaration>;
  failures: Map<ts.VariableDeclaration, string>;
}

const MUTATING_METHODS = new Set<string>(["set", "delete", "clear", "add", "push", "pop", "shift", "unshift", "splice", "fill", "copyWithin"]);
const READ_COLLECTION_METHODS = new Set<string>(["get", "has"]);
const PURE_STRING_METHODS = new Set<string>(["charCodeAt", "codePointAt", "slice", "substring", "includes", "startsWith", "endsWith", "indexOf", "lastIndexOf", "trim", "toLowerCase", "toUpperCase"]);
const FRESH_TYPED_ARRAY_MUTATORS = new Set<string>(["fill", "set", "copyWithin"]);

const isAssignmentOp = (k: ts.SyntaxKind): boolean =>
  k >= ts.SyntaxKind.FirstAssignment && k <= ts.SyntaxKind.LastAssignment;

/** Walk up past grouping/non-null/as wrappers around a node. */
function climbWrappers(n: ts.Node): ts.Node {
  let cur = n;
  while (cur.parent !== undefined && (ts.isParenthesizedExpression(cur.parent) ||
      ts.isNonNullExpression(cur.parent) || ts.isAsExpression(cur.parent)))
    cur = cur.parent;
  return cur;
}

type RefUsage =
  | { kind: "assignSelf"; expr: ts.BinaryExpression | ts.PrefixUnaryExpression | ts.PostfixUnaryExpression; rhs: ts.Expression | null }
  | { kind: "mutateProp"; access: ts.PropertyAccessExpression | ts.ElementAccessExpression; rhs: ts.Expression | null }
  | { kind: "mutateMethod"; call: ts.CallExpression; method: string }
  | { kind: "loadEntry"; call: ts.CallExpression }
  | { kind: "readMethod"; call: ts.CallExpression }
  | { kind: "readProp"; access: ts.PropertyAccessExpression | ts.ElementAccessExpression }
  | { kind: "test" }
  | { kind: "localAlias"; decl: ts.VariableDeclaration }
  | { kind: "escape"; at: ts.Node };

function classifyUsage(id: ts.Identifier): RefUsage {
  const cur = climbWrappers(id);
  const p = cur.parent;
  if (p === undefined) return { kind: "escape", at: id };
  if (ts.isBinaryExpression(p) && isAssignmentOp(p.operatorToken.kind) && p.left === cur)
    return { kind: "assignSelf", expr: p, rhs: p.right };
  if ((ts.isPrefixUnaryExpression(p) || ts.isPostfixUnaryExpression(p)) &&
      (p.operator === ts.SyntaxKind.PlusPlusToken || p.operator === ts.SyntaxKind.MinusMinusToken) && p.operand === cur)
    return { kind: "assignSelf", expr: p, rhs: null };
  if (ts.isVariableDeclaration(p) && p.initializer !== undefined && climbWrappers(p.initializer) === cur && ts.isIdentifier(p.name))
    return { kind: "localAlias", decl: p };
  if (ts.isBinaryExpression(p) && (p.operatorToken.kind === ts.SyntaxKind.EqualsEqualsEqualsToken ||
      p.operatorToken.kind === ts.SyntaxKind.ExclamationEqualsEqualsToken ||
      p.operatorToken.kind === ts.SyntaxKind.EqualsEqualsToken ||
      p.operatorToken.kind === ts.SyntaxKind.ExclamationEqualsToken))
    return { kind: "test" };
  if ((ts.isPrefixUnaryExpression(p) && p.operator === ts.SyntaxKind.ExclamationToken) ||
      (ts.isIfStatement(p) && p.expression === cur) ||
      (ts.isConditionalExpression(p) && p.condition === cur))
    return { kind: "test" };
  if ((ts.isPropertyAccessExpression(p) || ts.isElementAccessExpression(p)) && p.expression === cur) {
    const outer = climbWrappers(p);
    const gp = outer.parent;
    if (gp !== undefined && ts.isBinaryExpression(gp) && isAssignmentOp(gp.operatorToken.kind) && gp.left === outer)
      return { kind: "mutateProp", access: p, rhs: gp.right };
    if (gp !== undefined && (ts.isPrefixUnaryExpression(gp) || ts.isPostfixUnaryExpression(gp)) &&
        (gp.operator === ts.SyntaxKind.PlusPlusToken || gp.operator === ts.SyntaxKind.MinusMinusToken) && gp.operand === outer)
      return { kind: "mutateProp", access: p, rhs: null };
    if (gp !== undefined && ts.isDeleteExpression(gp) && gp.expression === outer)
      return { kind: "mutateProp", access: p, rhs: null };
    if (gp !== undefined && ts.isCallExpression(gp) && gp.expression === outer) {
      if (ts.isPropertyAccessExpression(p)) {
        if (MUTATING_METHODS.has(p.name.text)) return { kind: "mutateMethod", call: gp, method: p.name.text };
        if (p.name.text === "get") return { kind: "loadEntry", call: gp };
        if (READ_COLLECTION_METHODS.has(p.name.text)) return { kind: "readMethod", call: gp };
      }
      return { kind: "escape", at: gp };
    }
    return { kind: "readProp", access: p };
  }
  return { kind: "escape", at: p };
}

/** Collect all value-position identifier references in `scope` resolving to `decl`. */
function refsTo(decl: ts.VariableDeclaration, scope: ts.Node): ts.Identifier[] {
  if (!ts.isIdentifier(decl.name)) return [];
  const name = decl.name.text;
  const out: ts.Identifier[] = [];
  const walk = (n: ts.Node): undefined => {
    if (ts.isIdentifier(n) && n.text === name && n !== decl.name && isValueReference(n)) {
      const d = declOf(name, n);
      if (d !== null && d.kind !== "function" && d.kind !== "param" && d.at === decl) out.push(n);
    }
    n.forEachChild(walk);
    return undefined;
  };
  walk(scope);
  return out;
}

/** Check whether an expression stored into a container is freshly allocated
 * (directly, or a local variable assigned a fresh allocation immediately before
 * in the same block or initialized exclusively with fresh allocations). */
function isFreshStoredValue(expr: ts.Expression, scope: ts.Node, containerDecl: ts.VariableDeclaration): boolean {
  const u = unwrapExpr(expr);
  if (isFreshContainerAlloc(u)) return true;
  if (!ts.isIdentifier(u)) return false;
  const d = declOf(u.text, u);
  if (d === null || d.kind === "function" || d.kind === "param" || !ts.isVariableDeclaration(d.at)) return false;
  const vDecl = d.at;
  // Check if `vDecl` is a `const` initialized with a fresh container allocation.
  if (d.kind === "const" && isFreshContainerAlloc(d.init)) return true;
  // Or a `let` whose immediately preceding statement in the enclosing block
  // assigned a fresh container allocation (e.g. `cache = new Map(); map.set(k, cache)`).
  let stmt: ts.Node | undefined = expr;
  while (stmt !== undefined && !ts.isStatement(stmt)) stmt = stmt.parent;
  const blk = stmt?.parent;
  if (stmt !== undefined && blk !== undefined && ts.isBlock(blk)) {
    const idx = blk.statements.indexOf(stmt);
    if (idx > 0) {
      const prev = blk.statements[idx - 1];
      if (prev !== undefined && ts.isExpressionStatement(prev)) {
        const pe = unwrapExpr(prev.expression);
        if (ts.isBinaryExpression(pe) && pe.operatorToken.kind === ts.SyntaxKind.EqualsToken &&
            ts.isIdentifier(unwrapExpr(pe.left)) && unwrapExpr(pe.left).getText() === u.text &&
            declOf(u.text, pe.left)?.kind === "let" && isFreshContainerAlloc(pe.right))
          return true;
      }
    }
  }
  // Or every initializer/assignment to `vDecl` (other than loads from `containerDecl` itself) is fresh.
  const initOk = vDecl.initializer === undefined || isFreshContainerAlloc(vDecl.initializer) || isPrimitiveLiteral(vDecl.initializer);
  if (!initOk) return false;
  for (const r of refsTo(vDecl, scope)) {
    const use = classifyUsage(r);
    if (use.kind === "assignSelf") {
      if (use.rhs === null || !isFreshContainerAlloc(use.rhs)) return false;
    }
  }
  void containerDecl;
  return true;
}

const moduleConfinementCache = new Map<ts.SourceFile, ConfinedModuleInfo>();

function moduleConfinement(sf: ts.SourceFile): ConfinedModuleInfo {
  const cached = moduleConfinementCache.get(sf);
  if (cached !== undefined) return cached;
  const cells = new Set<ts.VariableDeclaration>();
  const containers = new Set<ts.VariableDeclaration>();
  const nestedLocals = new Set<ts.VariableDeclaration>();
  const failures = new Map<ts.VariableDeclaration, string>();

  // Collect all names exported from this module.
  const exported = new Set<string>();
  for (const st of sf.statements) {
    if (ts.isExportDeclaration(st) && st.moduleSpecifier === undefined && st.exportClause && ts.isNamedExports(st.exportClause))
      for (const e of st.exportClause.elements) exported.add(e.propertyName?.getText() ?? e.name.text);
    if (ts.isExportAssignment(st) && ts.isIdentifier(unwrapExpr(st.expression)))
      exported.add(unwrapExpr(st.expression).getText());
  }

  /** Whether any usage of local variable `vDecl` mutates through its value. */
  const localMutatedThrough = (vDecl: ts.VariableDeclaration, scope: ts.Node): boolean => {
    for (const r of refsTo(vDecl, scope)) {
      const u = classifyUsage(r);
      if (u.kind === "mutateProp" || u.kind === "mutateMethod") return true;
      if (u.kind === "localAlias" && localMutatedThrough(u.decl, scope)) return true;
    }
    return false;
  };

  /** Check whether a value loaded from a container (an expression like `c.get(k)` or `c[k]`)
   * is mutated anywhere, and if so, collect the local variable declarations holding it. */
  const analyzeLoadedExpr = (expr: ts.Expression): { mutated: boolean; escapes: boolean; localDecl: ts.VariableDeclaration | null; escapeAt: ts.Node | null } => {
    const cur = climbWrappers(expr);
    const p = cur.parent;
    if (p === undefined) return { mutated: false, escapes: true, localDecl: null, escapeAt: expr };
    // Directly assigned to a local variable: `let cache = m.get(k)`
    if (ts.isVariableDeclaration(p) && p.initializer !== undefined && climbWrappers(p.initializer) === cur && ts.isIdentifier(p.name)) {
      const fnScope = runnerOf(p) ?? sf;
      let mutated = false;
      let escapes = false;
      let escapeAt: ts.Node | null = null;
      for (const r of refsTo(p, fnScope)) {
        const u = classifyUsage(r);
        if (u.kind === "mutateProp" || u.kind === "mutateMethod") {
          mutated = true;
          // For `cache.set(k, v)`, values stored into nested container are payloads; check no escape of `cache`.
        } else if (u.kind === "assignSelf") {
          // Reassignment of the local variable (e.g. `cache = new Map()`) must be fresh!
          if (u.rhs === null || !isFreshContainerAlloc(u.rhs)) { escapes = true; escapeAt ??= u.expr; }
        } else if (u.kind === "escape") {
          // Storing `cache` back into the parent container (`graphemeEndCaches.set(p, cache)`) is checked separately by the caller!
          const parentCall = climbWrappers(r).parent;
          const backIntoParent = parentCall !== undefined && ts.isCallExpression(parentCall) &&
            ts.isPropertyAccessExpression(unwrapExpr(parentCall.expression)) &&
            unwrapExpr(parentCall.expression).getText().endsWith(".set") &&
            parentCall.arguments[1] !== undefined && climbWrappers(parentCall.arguments[1]) === climbWrappers(r);
          if (!backIntoParent) { escapes = true; escapeAt ??= u.at; }
        } else if (u.kind === "localAlias") {
          if (localMutatedThrough(u.decl, fnScope)) mutated = true;
          escapes = true; escapeAt ??= u.decl;
        }
      }
      return { mutated, escapes, localDecl: p, escapeAt };
    }
    // Directly mutated in place: `m.get(k)!.push(0)` or `m[k].x = 1`
    if ((ts.isPropertyAccessExpression(p) || ts.isElementAccessExpression(p)) && p.expression === cur) {
      const outer = climbWrappers(p);
      const gp = outer.parent;
      if (gp !== undefined && ((ts.isBinaryExpression(gp) && isAssignmentOp(gp.operatorToken.kind) && gp.left === outer) ||
          (ts.isCallExpression(gp) && gp.expression === outer && ts.isPropertyAccessExpression(p) && MUTATING_METHODS.has(p.name.text))))
        return { mutated: true, escapes: false, localDecl: null, escapeAt: null };
      return { mutated: false, escapes: false, localDecl: null, escapeAt: null };
    }
    // Returned or passed directly (e.g. `return map.get(k)`): escapes!
    return { mutated: false, escapes: true, localDecl: null, escapeAt: p };
  };

  for (const st of sf.statements) {
    if (!ts.isVariableStatement(st)) continue;
    const isExport = st.modifiers?.some((m) => m.kind === ts.SyntaxKind.ExportKeyword) ?? false;
    const isConst = (st.declarationList.flags & ts.NodeFlags.Const) !== 0;
    for (const decl of st.declarationList.declarations) {
      if (!ts.isIdentifier(decl.name)) continue;
      const name = decl.name.text;
      if (isExport || exported.has(name)) {
        failures.set(decl, `module binding ${name} is exported, not module-private`);
        continue;
      }
      if (!isFreshModuleInit(decl.initializer)) {
        failures.set(decl, `module binding ${name} is not initialized with a fresh or primitive value`);
        continue;
      }
      const refs = refsTo(decl, sf);
      if (!isConst) {
        // `let` binding: confined cell if never mutated through (nor any local alias mutated through).
        let mutatedThrough = false;
        let failReason: string | null = null;
        for (const r of refs) {
          const u = classifyUsage(r);
          if (u.kind === "mutateProp" || u.kind === "mutateMethod") {
            mutatedThrough = true;
            failReason ??= `module binding ${name} is mutated through at ${r.getText()}`;
          } else if (u.kind === "localAlias") {
            const fnScope = runnerOf(u.decl) ?? sf;
            if (localMutatedThrough(u.decl, fnScope)) {
              mutatedThrough = true;
              failReason ??= `alias ${u.decl.name.getText()} of module binding ${name} is mutated through`;
            }
          } else if (u.kind === "assignSelf") {
            // If `(b ??= e)` is bound to a local variable `const runs = b ??= e`, check that local too.
            const outer = climbWrappers(u.expr);
            const gp = outer.parent;
            if (gp !== undefined && ts.isVariableDeclaration(gp) && gp.initializer !== undefined &&
                climbWrappers(gp.initializer) === outer && ts.isIdentifier(gp.name)) {
              const fnScope = runnerOf(gp) ?? sf;
              if (localMutatedThrough(gp, fnScope)) {
                mutatedThrough = true;
                failReason ??= `alias ${gp.name.text} of module binding ${name} is mutated through`;
              }
            }
          }
        }
        if (!mutatedThrough) cells.add(decl);
        else failures.set(decl, failReason ?? `module binding ${name} is mutated through`);
      } else {
        // `const` container binding: must be freshly initialized container and never escape.
        if (!isFreshContainerAlloc(decl.initializer)) {
          failures.set(decl, `module const ${name} is not initialized with a fresh container`);
          continue;
        }
        let escapeReason: string | null = null;
        const loads: { mutated: boolean; escapes: boolean; localDecl: ts.VariableDeclaration | null; escapeAt: ts.Node | null }[] = [];
        const storedValues: { expr: ts.Expression; scope: ts.Node }[] = [];
        for (const r of refs) {
          const u = classifyUsage(r);
          if (u.kind === "escape" || u.kind === "localAlias" || u.kind === "assignSelf") {
            escapeReason ??= `module container ${name} escapes at ${r.parent?.getText() ?? r.getText()}`;
          } else if (u.kind === "loadEntry") {
            loads.push(analyzeLoadedExpr(u.call));
          } else if (u.kind === "readProp") {
            // Reading `.length` or `.size` is a scalar property, not an entry load.
            const isScalarMeta = ts.isPropertyAccessExpression(u.access) && (u.access.name.text === "length" || u.access.name.text === "size");
            if (!isScalarMeta) loads.push(analyzeLoadedExpr(u.access));
          } else if (u.kind === "mutateProp") {
            if (u.rhs !== null) storedValues.push({ expr: u.rhs, scope: runnerOf(r) ?? sf });
          } else if (u.kind === "mutateMethod") {
            if (u.method === "set" && u.call.arguments[1] !== undefined)
              storedValues.push({ expr: u.call.arguments[1], scope: runnerOf(r) ?? sf });
            else if ((u.method === "push" || u.method === "add" || u.method === "unshift") && u.call.arguments[0] !== undefined)
              storedValues.push({ expr: u.call.arguments[0], scope: runnerOf(r) ?? sf });
          }
        }
        if (escapeReason !== null) { failures.set(decl, escapeReason); continue; }
        const anyLoadedMutated = loads.some((l) => l.mutated);
        if (!anyLoadedMutated) {
          // Payload container (values stored are read-only after storage).
          containers.add(decl);
        } else {
          // Nested interior container: every stored value must be fresh, and NO loaded value may escape!
          let nestedFail: string | null = null;
          for (const s of storedValues)
            if (!isFreshStoredValue(s.expr, s.scope, decl))
              nestedFail ??= `module container ${name} stores non-fresh value ${s.expr.getText()} into a mutated nested interior`;
          for (const l of loads) {
            if (l.escapes)
              nestedFail ??= `nested interior loaded from module container ${name} escapes at ${l.escapeAt?.getText() ?? name}`;
            // Also check that values loaded one level deeper (from `l.localDecl`, e.g. `ends = cache.get(i)`) are not mutated after load.
            if (l.localDecl !== null) {
              const fnScope = runnerOf(l.localDecl) ?? sf;
              for (const lr of refsTo(l.localDecl, fnScope)) {
                const lu = classifyUsage(lr);
                if (lu.kind === "loadEntry") {
                  // Check `let ends = cache.get(i)`: allowed to be mutated ONLY after being overwritten with a fresh allocation!
                  const outer = climbWrappers(lu.call);
                  const gp = outer.parent;
                  if (gp !== undefined && ts.isVariableDeclaration(gp) && gp.initializer !== undefined &&
                      climbWrappers(gp.initializer) === outer && ts.isIdentifier(gp.name)) {
                    // Any mutation of `gp` must be preceded by a fresh assignment to `gp` in the same block!
                    for (const er of refsTo(gp, fnScope)) {
                      const eu = classifyUsage(er);
                      if ((eu.kind === "mutateProp" || eu.kind === "mutateMethod") && !isBlockFreshVar(er, gp, er))
                        nestedFail ??= `value loaded from nested interior of ${name} is mutated directly`;
                    }
                  }
                }
              }
            }
          }
          if (nestedFail !== null) { failures.set(decl, nestedFail); continue; }
          containers.add(decl);
          for (const l of loads) if (l.localDecl !== null) nestedLocals.add(l.localDecl);
        }
      }
    }
  }
  const info: ConfinedModuleInfo = { cells, containers, nestedLocals, failures };
  moduleConfinementCache.set(sf, info);
  return info;
}

/** Read a function declaration's stated effect:
 * - `Effects<P, T>` or `Modifies<OrdP, Effects<PaperP, T>>` (`checkBody: true`,
 *   must be verified against the function's body and module confinement), or
 * - `Modifies<OrdP, T>` (`checkBody: false`, certified by the ordinary pass). */
function statedEffect(decl: ts.FunctionDeclaration): { effect: Effect; checkBody: boolean } | null {
  const result = decl.type;
  if (result === undefined || !ts.isTypeReferenceNode(result) || !ts.isIdentifier(result.typeName)) return null;
  if (result.typeName.text === "Effects") {
    const p = result.typeArguments?.[0];
    const eff = p ? effectOf(p) : null;
    return eff === null ? null : { effect: eff, checkBody: true };
  }
  if (result.typeName.text === "Modifies") {
    const [ordP, retT] = result.typeArguments ?? [];
    if (retT !== undefined && ts.isTypeReferenceNode(retT) && ts.isIdentifier(retT.typeName) && retT.typeName.text === "Effects") {
      const paperP = retT.typeArguments?.[0];
      const eff = paperP ? effectOf(paperP) : null;
      return eff === null ? null : { effect: eff, checkBody: true };
    }
    const eff = ordP ? effectOf(ordP) : null;
    return eff === null ? null : { effect: eff, checkBody: false };
  }
  return null;
}

/** Cache of verified `Effects<P, T>` function declarations (`null` = ok, string = refusal). */
const verifiedEffects = new Map<ts.FunctionDeclaration, string | null>();
const verifyingEffects = new Set<ts.FunctionDeclaration>();

/** Verify a function declaration's body against its stated `Effects<P, T>`. */
function verifyStatedEffect(decl: ts.FunctionDeclaration, stated: Effect): string | null {
  const cached = verifiedEffects.get(decl);
  if (cached !== undefined) return cached;
  if (verifyingEffects.has(decl)) return null; // coinductive assumption for recursive self/mutual calls
  verifyingEffects.add(decl);
  const actual = closureEffect(decl, true, { owner: decl, names: boundedParams(decl) });
  verifyingEffects.delete(decl);
  const res = typeof actual === "string" ? actual : effectWithin(actual, stated);
  verifiedEffects.set(decl, res);
  return res;
}

/** Collect local `let` variables in `fn` whose initializer and every assignment
 * are exclusively fresh allocations or nullish literals (e.g. `let frag = null; ... frag = { ... }`),
 * and local fresh arrays (`const a = []`) whose only pushed/written elements are fresh allocations. */
function alwaysFreshLocals(fn: FnNode): { vars: Set<ts.Node>; elemArrays: Set<ts.Node> } {
  const vars = new Set<ts.Node>();
  const elemArrays = new Set<ts.Node>();
  if (fn.body === undefined) return { vars, elemArrays };
  const candidates: ts.VariableDeclaration[] = [];
  const collectDecls = (n: ts.Node): undefined => {
    if (n !== fn && isFn(n)) return undefined;
    if (ts.isVariableDeclaration(n) && ts.isIdentifier(n.name)) candidates.push(n);
    n.forEachChild(collectDecls);
    return undefined;
  };
  collectDecls(fn.body);
  // Fixed point so fresh arrays holding fresh locals (like `fragments.push(fragment)`) are recognized cleanly.
  for (let changed = true; changed;) {
    changed = false;
    for (const d of candidates) {
      if (!ts.isIdentifier(d.name)) continue;
      const isConst = (d.parent.flags & ts.NodeFlags.Const) !== 0;
      if (!vars.has(d)) {
        const initFresh = d.initializer === undefined || isPrimitiveLiteral(d.initializer) || isFreshContainerAlloc(d.initializer) ||
          (ts.isElementAccessExpression(unwrapExpr(d.initializer)) && (() => {
            const arr = unwrapExpr(d.initializer);
            if (!ts.isElementAccessExpression(arr) || !ts.isIdentifier(unwrapExpr(arr.expression))) return false;
            const ad = declOf(unwrapExpr(arr.expression).getText(), arr.expression);
            return ad !== null && ad.kind !== "function" && ad.kind !== "param" && elemArrays.has(ad.at);
          })());
        if (initFresh && (isConst ? !isPrimitiveLiteral(d.initializer) : true)) {
          let allFresh = true;
          let hasFresh = !isPrimitiveLiteral(d.initializer);
          for (const r of refsTo(d, fn.body)) {
            const u = classifyUsage(r);
            if (u.kind === "assignSelf") {
              if (u.rhs !== null && (isFreshContainerAlloc(u.rhs) || isPrimitiveLiteral(u.rhs))) {
                if (isFreshContainerAlloc(u.rhs)) hasFresh = true;
              } else { allFresh = false; break; }
            }
          }
          if (allFresh && hasFresh) { vars.add(d); changed = true; }
        }
      }
      if (isConst && !elemArrays.has(d) && d.initializer !== undefined &&
          ts.isArrayLiteralExpression(unwrapExpr(d.initializer)) &&
          unwrapExpr(d.initializer).getText() === "[]") {
        let allElemsFresh = true;
        for (const r of refsTo(d, fn.body)) {
          const u = classifyUsage(r);
          if (u.kind === "mutateMethod" && u.method === "push") {
            const arg = u.call.arguments[0];
            const ok = arg !== undefined && (isFreshContainerAlloc(arg) ||
              (ts.isIdentifier(unwrapExpr(arg)) && (() => {
                const ad = declOf(unwrapExpr(arg).getText(), arg);
                return ad !== null && ad.kind !== "function" && ad.kind !== "param" && vars.has(ad.at);
              })()));
            if (!ok) { allElemsFresh = false; break; }
          } else if (u.kind === "mutateMethod" || u.kind === "mutateProp") {
            allElemsFresh = false; break;
          }
        }
        if (allElemsFresh) { elemArrays.add(d); changed = true; }
      }
    }
  }
  return { vars, elemArrays };
}

/** Whether `target` is a fresh-element expression: an element read `arr[i]` of
 * an array in `elemArrays` (whose elements are all freshly allocated inside `fn`). */
function isFreshElementExpr(e: ts.Expression, elemArrays: ReadonlySet<ts.Node>): boolean {
  const u = unwrapExpr(e);
  if (!ts.isElementAccessExpression(u)) return false;
  const arr = unwrapExpr(u.expression);
  if (!ts.isIdentifier(arr)) return false;
  const d = declOf(arr.text, arr);
  return d !== null && d.kind !== "function" && d.kind !== "param" && elemArrays.has(d.at);
}

/** Whether an identifier expression refers to a variable that is fresh right at
 * `at` because an earlier statement in the same block assigned a fresh
 * allocation to it without an intervening reassignment. */
function isBlockFreshVar(id: ts.Identifier, declNode: ts.Node, at: ts.Node): boolean {
  let stmt: ts.Node | undefined = at;
  while (stmt !== undefined && !ts.isStatement(stmt)) stmt = stmt.parent;
  const blk = stmt?.parent;
  if (stmt === undefined || blk === undefined || !ts.isBlock(blk)) return false;
  const idx = blk.statements.indexOf(stmt);
  for (let i = idx - 1; i >= 0; i--) {
    const prev = blk.statements[i];
    if (prev === undefined) continue;
    if (ts.isExpressionStatement(prev)) {
      const pe = unwrapExpr(prev.expression);
      if (ts.isBinaryExpression(pe) && pe.operatorToken.kind === ts.SyntaxKind.EqualsToken &&
          ts.isIdentifier(unwrapExpr(pe.left)) && unwrapExpr(pe.left).getText() === id.text &&
          declOf(id.text, pe.left)?.kind === "let") {
        const d = declOf(id.text, pe.left);
        if (d !== null && d.kind === "let" && d.at === declNode) return isFreshContainerAlloc(pe.right);
      }
    }
    // Stop if another statement mentions this variable as an assignment target.
    if (assignedIn(id.text, prev)) return false;
  }
  return false;
}

function closureEffect(fn: FnNode, paramRoots: boolean = false, skip: Skip = noSkip): Effect | string {
  if (fn.body === undefined) return "has no body";
  const sf = fn.getSourceFile();
  const confined = moduleConfinement(sf);
  const { vars: freshVars, elemArrays: freshElemArrays } = alwaysFreshLocals(fn);
  const entries: [string, Change][] = [];
  let otherwise: Change = "keep";
  let error: string | null = null;
  const fail = (n: ts.Node, why: string): undefined => { error ??= `the callback's ${n.getText()} ${why}`; return undefined; };
  const keyOf = (r: { root: string; path: string[] }, tail: string): string => [r.root, ...r.path].join(".") + tail;

  /** Check whether an identifier refers to a confined module container or nested interior local. */
  const isConfinedContainerRef = (e: ts.Expression): boolean => {
    const u = unwrapExpr(e);
    if (!ts.isIdentifier(u)) return false;
    const d = declOf(u.text, u);
    if (d === null || d.kind === "function" || d.kind === "param" || !ts.isVariableDeclaration(d.at)) return false;
    return confined.containers.has(d.at) || confined.nestedLocals.has(d.at);
  };

  /** Check whether an expression is fresh at `at` (always-fresh local, block-fresh local, or fresh element). */
  const isFreshAt = (e: ts.Expression, at: ts.Node): boolean => {
    const u = unwrapExpr(e);
    if (isFreshContainerAlloc(u)) return true;
    if (isFreshElementExpr(u, freshElemArrays)) return true;
    if (ts.isIdentifier(u)) {
      const d = declOf(u.text, u);
      if (d !== null && d.kind !== "function" && d.kind !== "param" && within(d.at, fn)) {
        if (freshVars.has(d.at)) return true;
        if (isBlockFreshVar(u, d.at, at)) return true;
      }
    }
    return false;
  };

  const write = (target: ts.Expression, change: Change, at: ts.Node): undefined => {
    const t = unwrapExpr(target);
    if (ts.isPropertyAccessExpression(t) || ts.isElementAccessExpression(t)) {
      if (isConfinedContainerRef(t.expression)) {
        entries.push(["@state", "any"]);
        return undefined;
      }
      if (isFreshAt(t.expression, at)) return undefined;
      const base = resolve_(t.expression, fn, 0, paramRoots, freshVars);
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
      if (local) return undefined;
      if (d !== null && d.kind === "let" && ts.isVariableDeclaration(d.at) && confined.cells.has(d.at)) {
        entries.push(["@state", "any"]);
        return undefined;
      }
      const why = d !== null && d.kind !== "function" && d.kind !== "param" && ts.isVariableDeclaration(d.at)
        ? confined.failures.get(d.at) : undefined;
      return fail(at, why !== undefined ? `assigns a non-confined module binding (${why})` : "assigns a captured binding");
    }
    return fail(at, "writes a location no key of the instance can name");
  };
  const visitedHelpers = new Set<ts.Node>();
  const visit = (n: ts.Node): undefined => {
    if (error !== null) return undefined;
    if (n !== fn && isFn(n)) return undefined;
    if (ts.isBinaryExpression(n) && isAssignmentOp(n.operatorToken.kind))
      write(n.left, arithmetic.has(n.operatorToken.kind) ? "scalar" : "any", n);
    else if ((ts.isPrefixUnaryExpression(n) || ts.isPostfixUnaryExpression(n)) &&
        (n.operator === ts.SyntaxKind.PlusPlusToken || n.operator === ts.SyntaxKind.MinusMinusToken))
      write(n.operand, "scalar", n);
    else if (ts.isDeleteExpression(n)) write(n.expression, "any", n);
    else if (ts.isNewExpression(n)) {
      // A construction of a library global (`new RangeError(…)`, `new Map()`,
      // `new Int32Array(n)`): a fresh object, and the reviewed construct effect
      // of the overlay (rule Native); only an empty one is read here.
      const c = unwrapExpr(n.expression);
      const name = ts.isIdentifier(c) && declOf(c.text, c) === null && importedDecl(c.text, c) === undefined ? c.text : null;
      const gEntries = name === null ? [] : globalsOverlay.filter((g) => g.global === name && g.member === undefined &&
        (g.constructs === true || g.signature.startsWith("new ")));
      const okCollection = name !== null && COLLECTION_NAMES.has(name) && (n.arguments === undefined || n.arguments.length === 0);
      const okTypedArray = isFreshTypedArrayAlloc(n);
      if (!okCollection && !okTypedArray && (gEntries.length === 0 || !gEntries.every((g) => g.effect !== undefined && keepsHeap(g.effect))))
        return fail(n, "constructs an object whose reviewed effect may change old storage");
    }
    else if (ts.isCallExpression(n)) {
      const callee = unwrapExpr(n.expression);
      const skipped = ts.isIdentifier(callee) && skip.names.has(callee.text) && (() => {
        const d = declOf(callee.text, callee);
        return d !== null && d.kind === "param" && d.owner === skip.owner;
      })();
      if (ts.isPropertyAccessExpression(callee) && isConfinedContainerRef(callee.expression)) {
        const m = callee.name.text;
        if (READ_COLLECTION_METHODS.has(m)) {
          // Pure read on confined container (e.g. `cache.get(k)`, `cache.has(k)`).
        } else if (MUTATING_METHODS.has(m)) {
          entries.push(["@state", "any"]);
        } else return fail(n, `calls unrecognised method ${m} on a confined container`);
      } else if (ts.isPropertyAccessExpression(callee) && callee.name.text === "push") {
        // Rule Push: `push` of an array, by its declaration; a member named
        // `push` of any other object is an unknown method.
        if (isFreshAt(callee.expression, n)) {
          // Fresh local array push: `Fresh-Eff`.
        } else {
          const base = resolve_(callee.expression, fn, 0, paramRoots, freshVars);
          if (base === null) return fail(n, "pushes onto an array no key of the instance can name");
          const receiver = unwrapExpr(callee.expression);
          const array = base.fresh
            ? ts.isIdentifier(receiver) && (() => { const d = declOf(receiver.text, receiver); return d !== null && d.kind === "const" && isArrayLiteral(d.init); })()
            : isArrayAt(base, n);
          if (!array) return fail(n, "calls push of a value not declared an array, a method whose effect is not stated");
          if (!base.fresh) entries.push([keyOf(base, "[*]"), "extend"]);
        }
      } else if (ts.isPropertyAccessExpression(callee) && FRESH_TYPED_ARRAY_MUTATORS.has(callee.name.text) &&
          isFreshAt(callee.expression, n)) {
        // Mutator (`.fill`, `.set`, `.copyWithin`) on a fresh local typed array: `Fresh-Eff`.
      } else if (ts.isPropertyAccessExpression(callee) && callee.name.text === "subarray") {
        // `TypedArray.prototype.subarray` allocates a view without mutating any heap location.
      } else if (ts.isPropertyAccessExpression(callee) && PURE_STRING_METHODS.has(callee.name.text)) {
        // Pure string methods (`charCodeAt`, `slice`, `includes`, etc.) mutate no heap location.
      } else if (ts.isPropertyAccessExpression(callee) && callee.name.text === "join" &&
          (n.arguments.length === 0 || (n.arguments.length === 1 && n.arguments[0] !== undefined &&
            ts.isStringLiteral(unwrapExpr(n.arguments[0])))) &&
          (() => { const r = resolve_(callee.expression, fn, 0, paramRoots, freshVars); return r !== null && !r.fresh && isPrimitiveArrayAt(r, n); })()) {
        // `Array.prototype.join` on a primitive array with a string-literal (or omitted) separator runs no user `toString`.
      } else if (ts.isPropertyAccessExpression(callee) && callee.name.text === "test" &&
          ts.isRegularExpressionLiteral(unwrapExpr(callee.expression)) &&
          !/[gy]/.test(unwrapExpr(callee.expression).getText().split("/").pop() ?? "")) {
        // Non-global, non-sticky regex literal `.test(...)` mutates no old storage.
      } else if (skipped) {
        // A call of a bounded callback parameter: its effect is the effect
        // variable's, which the caller's instance gives.
      } else if (ts.isIdentifier(callee)) {
        const d = declOf(callee.text, callee);
        // A call to a local `const` helper closure declared inside `fn` (e.g. `const varint = () => ...`):
        // inline its body under `fn`'s own local scope.
        if (d !== null && d.kind === "const" && within(d.at, fn) && d.init !== undefined && isFn(unwrapExpr(d.init))) {
          const helper = unwrapExpr(d.init);
          if (isFn(helper) && helper.body !== undefined && !visitedHelpers.has(helper)) {
            visitedHelpers.add(helper);
            for (const p of helper.parameters) visit(p);
            visit(helper.body);
          }
        } else {
          const decl = d?.kind === "function" ? d.node : d === null ? importedDecl(callee.text, callee) : undefined;
          // Bare global library function (e.g. `atob`): checked against reviewed `globalsOverlay`.
          if (d === null && decl === undefined) {
            const gEntries = globalsOverlay.filter((g) => g.global === callee.text && g.member === undefined &&
              g.constructs !== true && !g.signature.startsWith("new "));
            if (gEntries.length > 0 && gEntries.every((g) => g.effect !== undefined && keepsHeap(g.effect))) {
              n.forEachChild(visit);
              return undefined;
            }
          }
          const st = decl === undefined ? null : statedEffect(decl);
          if (decl !== undefined && st !== null && st.checkBody) {
            const why = verifyStatedEffect(decl, st.effect);
            if (why !== null) return fail(n, `calls ${callee.text} whose stated Effects failed verification (${why})`);
          }
          // A call of a function with effect parameters whose instances are the
          // calling function's own effect parameters (or joins `[E, P]`), or
          // omitted where every callback parameter bounded by that effect
          // variable receives `undefined` or is omitted: its effect is its own
          // effect besides them, read from its body, and any forwarded variables,
          // which the calling function's bound accounts for.
          const outer = effectVars(fn);
          const positions = decl === undefined ? [] : (decl.typeParameters ?? []).flatMap((tp, i) => effectVars(decl).includes(tp.name.text) ? [i] : []);
          const isOmittedOrUndef = (a: ts.Expression | undefined): boolean =>
            a === undefined || unwrapExpr(a).kind === ts.SyntaxKind.UndefinedKeyword ||
            (ts.isIdentifier(unwrapExpr(a)) && unwrapExpr(a).getText() === "undefined");
          const declBoundedBy = (eName: string): number[] => {
            if (decl === undefined) return [];
            const idxs: number[] = [];
            decl.parameters.forEach((p, idx) => {
              if (p.type === undefined) return;
              const seen = new Set<string>();
              mentions(p.type, seen);
              if (seen.has(eName)) idxs.push(idx);
            });
            return idxs;
          };
          const forwards = decl !== undefined && st === null && positions.length > 0 &&
            positions.every((i) => {
              const t = n.typeArguments?.[i];
              if (t === undefined) {
                const eName = decl.typeParameters?.[i]?.name.text;
                if (eName === undefined) return false;
                const bIdxs = declBoundedBy(eName);
                return bIdxs.length > 0 && bIdxs.every((idx) => isOmittedOrUndef(n.arguments[idx]));
              }
              if (ts.isTypeReferenceNode(t) && ts.isIdentifier(t.typeName) && outer.includes(t.typeName.text)) return true;
              const jp = joinParts(t);
              if (jp !== null) {
                const [vEl, pEl] = jp;
                return ts.isTypeReferenceNode(vEl) && ts.isIdentifier(vEl.typeName) &&
                  outer.includes(vEl.typeName.text) && effectOf(pEl) !== null;
              }
              return false;
            });
          const pureEff: Effect = { entries: [], else: "keep" };
          const eff = st !== null ? st.effect
            : decl !== undefined && isIdentityFn(decl) ? pureEff
            : forwards && decl !== undefined && !reading.has(decl) ? (() => {
              reading.add(decl);
              const e = closureEffect(decl, true, { owner: decl, names: boundedParams(decl) });
              reading.delete(decl);
              return typeof e === "string" ? null : e;
            })() : null;
          if (decl === undefined || eff === null) return fail(n, "calls a function whose effect is not stated");
          const params = decl.parameters.map((q) => ts.isIdentifier(q.name) ? q.name.text : "");
          for (const [k, c] of eff.entries) {
            if (k === "@state") { entries.push(["@state", c]); continue; }
            const at = params.indexOf(rootOf(k));
            const arg = n.arguments[at];
            const paramDecl = decl.parameters[at];
            if (arg !== undefined && isPrimitiveLiteral(arg)) {
              // Primitive literal (e.g. `null`, `undefined`, number, string): no heap locations.
              continue;
            }
            if (arg === undefined && paramDecl !== undefined && isFreshContainerAlloc(paramDecl.initializer)) {
              // Omitted parameter with fresh allocation default (e.g. `stats = { ... }`): own locations are fresh.
              const own = /^(?:\.[A-Za-z_$][\w$]*|\.\*|\[\*\]|\[#\])$/.test(restOf(k));
              if (!own) return fail(n, `omits ${rootOf(k)} whose default's held storage ${k} may change`);
              continue;
            }
            if (arg !== undefined && isFreshAt(arg, n)) {
              const own = /^(?:\.[A-Za-z_$][\w$]*|\.\*|\[\*\]|\[#\])$/.test(restOf(k));
              if (!own) return fail(n, `passes to ${rootOf(k)} a fresh object whose held storage ${k} may change`);
              continue;
            }
            const base = arg === undefined ? null : resolve_(arg, fn, 0, paramRoots, freshVars);
            if (base === null) return fail(n, `passes to ${rootOf(k)} a value no key of the instance can name`);
            // A fresh object's own fields and spine are no change of older
            // storage; a location through one of its fields may be.
            const own = /^(?:\.[A-Za-z_$][\w$]*|\.\*|\[\*\]|\[#\])$/.test(restOf(k));
            if (base.fresh && !own) return fail(n, `passes to ${rootOf(k)} a fresh object whose held storage ${k} may change`);
            if (!base.fresh) entries.push([keyOf(base, restOf(k)), c]);
          }
          // If forwarding `[E, P]` or `Join<E, P>`, include `P`'s entries in the caller's own effect too.
          if (forwards)
            for (const i of positions) {
              const t = n.typeArguments?.[i];
              const jp = t === undefined ? null : joinParts(t);
              if (jp !== null) {
                const extra = effectOf(jp[1]);
                if (extra !== null) {
                  for (const [k, c] of extra.entries) entries.push([k, c]);
                  if (!le(extra.else, otherwise)) otherwise = extra.else;
                }
              }
            }
          if (!le(eff.else, otherwise)) otherwise = eff.else;
        }
      } else if (ts.isPropertyAccessExpression(callee) && ts.isIdentifier(callee.expression) &&
          declOf(callee.expression.text, callee) === null && importedDecl(callee.expression.text, callee) === undefined) {
        // A member of a library global (`Math.max`): its effect is the
        // reviewed one of the library-globals overlay (rule Native); a
        // member whose reviewed effect keeps the heap changes nothing.
        const global = callee.expression.text;
        const member = callee.name.text;
        const gEntries = globalsOverlay.filter((g) => g.global === global && g.member === member);
        if (gEntries.length === 0 || !gEntries.every((g) => g.effect !== undefined && keepsHeap(g.effect)))
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

/** Extract `[E, P]` from either a tuple `[E, P]` or `Join<E, P>`. */
function joinParts(t: ts.TypeNode): [ts.TypeNode, ts.TypeNode] | null {
  if (ts.isTupleTypeNode(t) && t.elements.length === 2 && t.elements[0] !== undefined && t.elements[1] !== undefined)
    return [t.elements[0], t.elements[1]];
  if (ts.isTypeReferenceNode(t) && ts.isIdentifier(t.typeName) && t.typeName.text === "Join" &&
      t.typeArguments?.length === 2 && t.typeArguments[0] !== undefined && t.typeArguments[1] !== undefined)
    return [t.typeArguments[0], t.typeArguments[1]];
  return null;
}

/** The access paths of an effect's reach entry, open where not read. */
const accAt = (e: Effect, key: string): Acc => accFromJson(e.reach?.[key]);

/** Whether a claim's location covers an effect's location: the same
 * location, a field among the fields `x.*`, a location in the reach
 * `x.**` at an access path of its type, or confined module state `@state`. */
function covers(c: Loc, r: Loc, acc: Acc): boolean {
  if (c.kind === "modState" || r.kind === "modState") return c.kind === "modState" && r.kind === "modState";
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
    callerParams: Set<string>, anchFresh: Set<string> = new Set()): string | null {
  // The empty effect is within every bound, whatever its arguments.
  if (instance.entries.length === 0 && instance.else === "keep") return null;
  const actual = (key: string): string | null => {
    if (key === "@state") return "@state";
    const at = params.indexOf(rootOf(key));
    if (at < 0) return key;
    const arg = args[at];
    return arg === null || arg === undefined ? null : arg + restOf(key);
  };
  const ownOf = (l: Loc): boolean => l.path.length === 0 && (l.kind === "field" || l.kind === "fields" || l.kind === "spine");
  // When forwarding an outer effect variable E, rule Anch + Meet guarantees
  // that every anchored instance of E keeps every own location of any external
  // object freshly allocated inside the caller (`anchFresh`).
  const anchoredFresh = (b: Loc): boolean => anchFresh.has(b.root) && ownOf(b);
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
      if (!anchoredFresh(b) && !disjoint(l, b, l.kind === "reach" ? iacc : bacc, fresh, callerParams) && !le(c, d))
        return `the instance changes ${r} by ${c}; the bound allows ${text}: ${d}`;
    if (bound.else !== "any" && !bs.some(([b, , , bacc]) => inside(l, b, bacc, iacc)) && !le(c, bound.else))
      return `the instance changes ${r} by ${c}; the bound's else allows ${bound.else}`;
  }
  // The instance's `else` reaches the locations of a bound entry that no
  // instance entry covers: the same location, or one inside an instance
  // reach, or an own location of a caller-allocated object kept by Anch.
  const covered = (b: Loc, bacc: Acc): boolean => anchoredFresh(b) || is.some(([l, , iacc]) =>
    (l.kind === "reach" && b.kind === "reach" ? reachInside(b, bacc, l, iacc)
      : l.kind === b.kind && l.key === b.key && pathText(l) === pathText(b)) || inside(b, l, iacc, bacc));
  for (const [b, d, text, bacc] of bs)
    if (!covered(b, bacc) && !le(instance.else, d)) return `the instance's else ${instance.else} exceeds the bound's ${text}: ${d}`;
  if (!le(instance.else, bound.else)) return `the instance's else ${instance.else} exceeds the bound's else ${bound.else}`;
  return null;
}

/** Whether an instance is anchored as the prototype decides it
(Definition "Instances and anchoring", generalized for confined module state
`@state` per `Model.confined_rule`): its `else` is `keep`, it has no class
key, and each key is `@state` or a field, the fields or the spine of a
variable that is a `const` or a parameter its function never assigns; the
reason otherwise. */
function anchored(instance: Effect, at: ts.Node): string | null {
  if (instance.classes) return "an instance has no class key (values, spines): such regions are not anchored";
  if (instance.else !== "keep") return `an instance's else is keep; this one's is ${instance.else}, which changes storage allocated after the call`;
  for (const [k] of instance.entries) {
    const l = locOf(k);
    if (l !== null && l.kind === "modState") continue;
    if (l === null || l.path.length > 0 || !(l.kind === "field" || l.kind === "fields" || l.kind === "spine"))
      return `the instance's key ${k} is not a field, the fields, the spine of a variable, or @state, which the prototype decides anchored`;
    const d = declOf(l.root, at);
    const rigid = d !== null && (d.kind === "const" || (d.kind === "param" && !assignedIn(l.root, d.owner)));
    if (!rigid) return `the instance's key ${k} is rooted at ${l.root}, which is no const or unassigned parameter`;
  }
  return null;
}

/** The effect variable a callback parameter's type gives its calls, null
where the type mentions no effect variable, or the reason the prototype
does not read it. Read is a function type, a local alias of one, or a union
of one with `undefined` or `null`, whose result is `Modifies<E, T>`, `E` the
variable, and whose parameters and `T` do not mention it. */
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
      if (p.type !== undefined && mentionsName(p.type, x))
        return `the callback type uses its effect variable in the parameter ${p.name.getText()}`;
    const r = f.type;
    if (r === undefined) return "the callback type has no result type";
    if (!ts.isTypeReferenceNode(r) || !ts.isIdentifier(r.typeName) || r.typeName.text !== "Modifies")
      return `the callback type states no effect Modifies<${x}, T>`;
    const [eff, result] = r.typeArguments ?? [];
    if (eff === undefined || (result !== undefined && mentionsName(result, x))) return "the callback type's Modifies is not read";
    return isVar(eff, x) ? null : "the callback's stated effect is not its effect variable";
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

/** Whether bounded callback parameter `paramName` of `decl` never escapes
 * `decl`'s dynamic extent (rule Callback-Inv): every value-position reference
 * in `decl` is either a direct call (`cb(...)` / `cb?.(...)`), a pure
 * nullish/truthiness test (`!cb`, `typeof cb`, `cb === undefined`, `if (cb)`,
 * `cb ? ... : ...`, left operand of `cb && ...`), or forwarded directly as an
 * argument to a non-escaping parameter of a local/imported function
 * declaration. Nested closures capturing `paramName`, assignments, field/array
 * stores, returns, throws, and calls to unverified callees are all refused. */
function nonEscapingCallback(decl: ts.FunctionDeclaration, paramName: string, visiting: Set<string> = new Set()): boolean {
  if (decl.body === undefined) return false;
  const key = `${decl.getSourceFile().fileName}:${decl.pos}:${paramName}`;
  if (visiting.has(key)) return true;
  visiting.add(key);
  let ok = true;
  const checkRef = (id: ts.Identifier): boolean => {
    const cur = climbWrappers(id);
    const p = cur.parent;
    if (p === undefined) return false;
    if (ts.isCallExpression(p) && p.expression === cur) return true;
    if (ts.isPrefixUnaryExpression(p) && p.operator === ts.SyntaxKind.ExclamationToken) return true;
    if (ts.isTypeOfExpression(p)) return true;
    if (ts.isIfStatement(p) && p.expression === cur) return true;
    if (ts.isConditionalExpression(p) && p.condition === cur) return true;
    if (ts.isBinaryExpression(p)) {
      const op = p.operatorToken.kind;
      if (op === ts.SyntaxKind.EqualsEqualsEqualsToken || op === ts.SyntaxKind.ExclamationEqualsEqualsToken ||
          op === ts.SyntaxKind.EqualsEqualsToken || op === ts.SyntaxKind.ExclamationEqualsToken)
        return true;
      if (op === ts.SyntaxKind.AmpersandAmpersandToken && p.left === cur) return true;
    }
    if (ts.isCallExpression(p)) {
      const argIdx = p.arguments.findIndex((a) => a === cur);
      if (argIdx >= 0 && !p.arguments.slice(0, argIdx).some(ts.isSpreadElement)) {
        const callee = unwrapExpr(p.expression);
        if (ts.isIdentifier(callee)) {
          const d = declOf(callee.text, callee);
          const target = d?.kind === "function" ? d.node : d === null ? importedDecl(callee.text, callee) : undefined;
          const targetParam = target?.parameters[argIdx];
          if (target !== undefined && targetParam !== undefined && ts.isIdentifier(targetParam.name) &&
              targetParam.dotDotDotToken === undefined && targetParam.initializer === undefined)
            return nonEscapingCallback(target, targetParam.name.text, visiting);
        }
      }
    }
    return false;
  };
  const walk = (n: ts.Node): undefined => {
    if (!ok) return undefined;
    if (n !== decl && isFn(n)) {
      const checkNested = (m: ts.Node): undefined => {
        if (!ok) return undefined;
        if (ts.isIdentifier(m) && m.text === paramName && isValueReference(m)) {
          const d = declOf(m.text, m);
          if (d !== null && d.kind === "param" && d.owner === decl) ok = false;
        }
        m.forEachChild(checkNested);
        return undefined;
      };
      checkNested(n);
      return undefined;
    }
    if (ts.isIdentifier(n) && n.text === paramName && isValueReference(n)) {
      const d = declOf(n.text, n);
      if (d !== null && d.kind === "param" && d.owner === decl && !checkRef(n)) ok = false;
    }
    n.forEachChild(walk);
    return undefined;
  };
  for (const p of decl.parameters) if (p.initializer !== undefined) walk(p.initializer);
  walk(decl.body);
  visiting.delete(key);
  return ok;
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
        reach[k] = accJson(accOf(p?.type, tree));
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
    // Verify any stated `Effects<P, T>` on this function against its body and
    // module confinement obligations (`OwnerConfined`).
    const st = statedEffect(s);
    let stated: Effect | undefined;
    if (st !== null && st.checkBody && refusal === undefined) {
      const why = verifyStatedEffect(s, st.effect);
      if (why !== null) refusal = `stated Effects verification failed: ${why}`;
      else {
        const reach: Record<string, AccJson> = {};
        for (const [k] of st.effect.entries) {
          const l = locOf(k);
          if (l?.kind !== "reach") continue;
          const p = l.path.length === 0 ? s.parameters[params.indexOf(l.root)] : undefined;
          reach[k] = accJson(accOf(p?.type, tree));
        }
        if (Object.keys(reach).length > 0) st.effect.reach = reach;
        stated = st.effect;
      }
    }
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
    const nonEscaping = refusal !== undefined || bounded.length === 0 ? []
      : bounded.map((b) => b.param).filter((name) => name !== "" && nonEscapingCallback(s, name));
    const info: FunctionInfo = { typeParams: (s.typeParameters ?? []).map((tp) => tp.name.text), params, effectParams, bounded };
    if (own !== undefined) info.own = own;
    if (stated !== undefined) info.stated = stated;
    if (nonEscaping.length > 0) info.nonEscaping = nonEscaping;
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
      assumes.push({ caller, line,
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
        const forwardedExtra = new Map<string, Effect>();
        const empty = new Set<string>();
        let reason: string | null = null;
        callee.effectParams.forEach((e) => {
          const arg = n.typeArguments?.[callee.typeParams.indexOf(e.name)];
          const eff = arg ? effectOf(arg) : null;
          const variable = arg !== undefined && ts.isTypeReferenceNode(arg) && ts.isIdentifier(arg.typeName)
            ? outer?.effectParams.find((o) => o.name === arg.typeName.getText()) : undefined;
          // A join instance `[E, P]` or `Join<E, P>` forwarding an outer effect variable `E`
          // joined with a closed anchored effect `P` (e.g. `Join<E, { "@state": "any" }>`).
          const joinTuple = arg !== undefined ? (() => {
            const jp = joinParts(arg);
            if (jp === null) return null;
            const [vEl, pEl] = jp;
            if (!ts.isTypeReferenceNode(vEl) || !ts.isIdentifier(vEl.typeName)) return null;
            const v = outer?.effectParams.find((o) => o.name === vEl.typeName.getText());
            const p = effectOf(pEl);
            return v !== undefined && p !== null ? { variable: v, extra: p } : null;
          })() : null;
          const none = callee.bounded.filter((b) => b.variable === e.name).every((b) => {
            const a = n.arguments[b.index];
            return a === undefined || unwrapExpr(a).kind === ts.SyntaxKind.UndefinedKeyword ||
              ts.isIdentifier(unwrapExpr(a)) && unwrapExpr(a).getText() === "undefined";
          });
          if (eff) {
            instance[e.name] = eff;
            reason ??= anchored(eff, n);
          } else if (variable) { instance[e.name] = variable.bound; forwarded.set(e.name, variable.name); }
          else if (joinTuple !== null) {
            instance[e.name] = joinTuple.variable.bound;
            forwarded.set(e.name, joinTuple.variable.name);
            forwardedExtra.set(e.name, joinTuple.extra);
            reason ??= anchored(joinTuple.extra, n);
          } else if (arg === undefined && none) { instance[e.name] = { entries: [], else: "keep" }; empty.add(e.name); }
        });
        const args = n.arguments.map((a) => argPath(a));
        // The caller's parameters it never assigns: their values and own
        // locations are apart from what the caller allocates.
        const callerParamList = unit.parameters.map((q) => ts.isIdentifier(q.name) ? q.name.text : "");
        const callerParams = new Set(callerParamList.filter((q) => q !== "" && !assignedIn(q, unit)));
        const isCallerParamKey = (k: string): boolean => {
          if (k === "@state") return true;
          const r = rootOf(k);
          if (!callerParams.has(r)) return false;
          return k.endsWith(".**") || k.endsWith("[*]") || k.endsWith("[#]") || k.endsWith(".*") ||
            k.split(".").length === 2;
        };
        const normalizeEffect = (written: Effect): { inst: Effect; fresh: Set<string> } | string => {
          const fresh = new Set<string>();
          const entries: [string, Change][] = [];
          const reach: Record<string, AccJson> = {};
          for (const [k, c] of written.entries) {
            const norm = normalizeKey(k, n, unit);
            if (norm === null) return `the instance's key ${k} names no variable of the caller`;
            if (norm.fresh) fresh.add(rootOf(norm.key));
            entries.push([norm.key, c]);
            const a = written.reach?.[k];
            if (a !== undefined) reach[norm.key] = a;
          }
          const inst: Effect = Object.keys(reach).length > 0 ? { entries, else: written.else, reach } : { entries, else: written.else };
          return { inst, fresh };
        };
        const normalizedInst = new Map<string, Effect>();
        const normalizedExtra = new Map<string, Effect>();
        for (const e of callee.effectParams) {
          if (reason !== null) break;
          const written = instance[e.name];
          if (written === undefined) { reason = `no instance written for ${e.name}`; break; }
          // The instance's roots resolved at the call: aliases replaced by
          // the paths they hold, and the objects the caller allocated.
          const normRes = normalizeEffect(written);
          if (typeof normRes === "string") { reason = normRes; break; }
          const { inst, fresh } = normRes;
          normalizedInst.set(e.name, inst);
          const extraRaw = forwardedExtra.get(e.name);
          const extraNorm = extraRaw === undefined ? null : normalizeEffect(extraRaw);
          if (typeof extraNorm === "string") { reason = extraNorm; break; }
          if (extraNorm !== null) normalizedExtra.set(e.name, extraNorm.inst);
          for (const b of callee.bounded.filter((x) => x.variable === e.name)) {
            if (empty.has(e.name)) break;
            let arg: ts.Expression | undefined = n.arguments[b.index];
            // A forwarded variable (or join `[E, P]`): the callback is one of
            // the calling function's own callbacks of that variable, or a
            // closure whose effect besides calls to them lies within `P`
            // (empty when bare `E`).
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
              if (extraNorm !== null) {
                reason = typeof eff === "string" ? eff : effectWithin(eff, extraNorm.inst);
              } else {
                reason = typeof eff === "string" ? eff
                  : eff.entries.length > 0 || eff.else !== "keep"
                    ? `the callback also changes ${eff.entries.map(([k, c]) => `${k} by ${c}`).join(", ") || `else ${eff.else}`}, which ${e.name} forwarded as ${caller}'s effect variable ${outerVar} does not allow`
                    : null;
              }
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
          // When forwarding an outer effect variable E, rule Anch + Meet keeps
          // every own location of any external `const` object allocated in the
          // caller's body (`anchFresh`).
          const anchFresh = new Set<string>();
          if (forwarded.has(e.name)) {
            for (const a of args) {
              if (a === null || a.includes(".")) continue;
              const d = declOf(a, n);
              if (d !== null && d.kind === "const" && within(d.at, unit) && isAllocation(d.init)) anchFresh.add(a);
            }
          }
          reason = instCheck(inst, e.bound, callee.params, args, fresh, callerParams, anchFresh);
          if (reason === null && extraNorm !== null)
            reason = instCheck(extraNorm.inst, e.bound, callee.params, args, extraNorm.fresh, callerParams);
        }
        // The call's effect at the caller (Inst's conclusion) is within the
        // instances (or their bounds where an instance names caller locals or
        // forwarded variables) and the callee's own effect; an empty instance
        // stands for its bound exactly.
        const calleeBounds: Effect[] = [];
        const callerBounds: Effect[] = [];
        for (const e of callee.effectParams) {
          if (empty.has(e.name)) {
            calleeBounds.push(instance[e.name] ?? e.bound);
            continue;
          }
          const inst = normalizedInst.get(e.name);
          const extra = normalizedExtra.get(e.name);
          if (reason === null && inst !== undefined &&
              inst.entries.every(([k]) => isCallerParamKey(k)) &&
              (extra === undefined || extra.entries.every(([k]) => isCallerParamKey(k)))) {
            callerBounds.push(inst);
            if (extra !== undefined) callerBounds.push(extra);
          } else {
            calleeBounds.push(e.bound);
          }
        }
        // Inline closures passed directly to verified non-escaping bounded
        // callback parameters of `callee` (rule Callback-Inv).
        const scopedCallbacks: { span: [number, number]; paramIndex: number }[] = [];
        if (reason === null && callee.refusal === undefined && callee.nonEscaping !== undefined) {
          for (const b of callee.bounded) {
            if (!callee.nonEscaping.includes(b.param)) continue;
            const rawArg = n.arguments[b.index];
            const passed = rawArg === undefined ? undefined : unwrapExpr(rawArg);
            if (passed !== undefined && (ts.isArrowFunction(passed) || ts.isFunctionExpression(passed)))
              scopedCallbacks.push({ span: [passed.getStart(), passed.getEnd()], paramIndex: b.index });
          }
        }
        calls.push({ caller, callee: n.expression.text, instance, ok: reason === null, reason,
          params: callee.params, bounds: calleeBounds,
          ...(callerBounds.length > 0 ? { callerParams: callerParamList, callerBounds } : {}),
          ...(scopedCallbacks.length > 0 ? { scopedCallbacks } : {}),
          own: callee.own ?? "has no effect parameters", span: [n.getStart(), n.getEnd()] });
      } else if (callee && callee.stated !== undefined && callee.refusal === undefined) {
        // A call to a monomorphic function with a verified `Effects<P, T>`
        // (e.g. `Effects<{ "@state": "any" }, T>`): frame its caller's external
        // facts and read links against `P` via rule Confined.
        calls.push({ caller, callee: n.expression.text, instance: {}, ok: true, reason: null,
          params: callee.params, bounds: [], own: callee.stated, span: [n.getStart(), n.getEnd()] });
      }
    }
    n.forEachChild(visit);
    return undefined;
  };
  visit(tree);
  closeParser();
  importedFiles.clear();
  moduleConfinementCache.clear();
  verifiedEffects.clear();
  verifyingEffects.clear();
  typeDeclsOf.clear();
  return { functions, calls, assumes, refusals };
}

if (process.argv[1] && resolve(process.argv[1]) === import.meta.filename) {
  const file = process.argv[2];
  if (file === undefined) {
    process.stderr.write("usage: node dev/paper-annotations.mts file.ts\n");
    process.exitCode = 2;
  } else process.stdout.write(JSON.stringify(annotations(resolve(file)), null, 2) + "\n");
}
