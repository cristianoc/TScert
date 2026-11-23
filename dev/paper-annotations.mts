// The paper's annotations in a source file, for the experimental prototype of
// docs/drafts/paper-rules-mode.md: each function's effect type parameters
// with their `AtMost<P>` bounds and the parameters whose types mention them,
// and each call that writes an instance of such a parameter, with the check
// of the instance against the bound (rule Inst). The ordinary front end reads
// none of this: `AtMost` is a local alias of `unknown` there.
//   node dev/paper-annotations.mts file.ts
import { readFileSync } from "node:fs";
import { resolve } from "node:path";
import { close as closeParser, openText } from "../tools/fragment-parse.mts";
import { syntax as ts } from "../tools/syntax.mts";

/** A change of the paper, in its order. */
const changes = ["keep", "init", "scalar", "extend", "grow", "any"] as const;
type Change = (typeof changes)[number];
const isChange = (s: string): s is Change => changes.some((c) => c === s);
const le = (a: Change, b: Change): boolean => changes.indexOf(a) <= changes.indexOf(b);

/** An effect of the paper: entries in the `Modifies` key syntax, and `else`;
for a bound with a reach entry `"x.**"`, the keys its types declare. */
interface Effect { entries: [string, Change][]; else: Change; reachKeys?: string[] }

interface EffectParam { name: string; bound: Effect }
interface FunctionInfo { params: string[]; effectParams: EffectParam[]; bounded: { param: string; index: number; variable: string }[] }
interface CallInfo { caller: string; callee: string; instance: Record<string, Effect>; ok: boolean; reason: string | null }

/** The effect a string literal type `'{ "x[*]": "keep", "else": "any" }'`
 * holds as JSON. */
function effectOfText(text: string): Effect | null {
  let parsed: unknown;
  try { parsed = JSON.parse(text); } catch { return null; }
  if (typeof parsed !== "object" || parsed === null || Array.isArray(parsed)) return null;
  const entries: [string, Change][] = [];
  let otherwise: Change = "keep";
  for (const [key, value] of Object.entries(parsed)) {
    if (typeof value !== "string" || !isChange(value)) return null;
    if (key === "else") otherwise = value;
    else entries.push([key, value]);
  }
  return { entries, else: otherwise };
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
  for (const m of node.members) {
    if (!ts.isPropertySignatureDeclaration(m) || !m.type || !ts.isLiteralTypeNode(m.type)) return null;
    const literal = m.type.literal;
    if (!ts.isStringLiteral(literal) || !isChange(literal.text)) return null;
    const name = m.name;
    if ((ts.isIdentifier(name) || ts.isStringLiteral(name)) && name.text === "else") otherwise = literal.text;
    else if (ts.isStringLiteral(name)) entries.push([name.text, literal.text]);
    else return null;
  }
  return { entries, else: otherwise };
}

/** The keys a type declares and, through them, the types it holds
(`docs/drafts/effect-languages.md`, "Declared reach"): the members of a type
literal or an interface, the element type of an array, the members of a
union, and a type alias or interface named in the same file. */
function declaredKeys(node: ts.TypeNode | undefined, decls: Map<string, ts.Node>, seen: Set<string>, out: Set<string>): void {
  if (!node) return;
  if (ts.isTypeReferenceNode(node) && ts.isIdentifier(node.typeName)) {
    const name = node.typeName.text;
    const decl = decls.get(name);
    if (decl === undefined || seen.has(name)) return;
    seen.add(name);
    if (ts.isTypeAliasDeclaration(decl)) declaredKeys(decl.type, decls, seen, out);
    else if (ts.isInterfaceDeclaration(decl)) membersKeys(decl.members, decls, seen, out);
    return;
  }
  if (ts.isTypeLiteralNode(node)) membersKeys(node.members, decls, seen, out);
  else if (ts.isArrayTypeNode(node)) declaredKeys(node.elementType, decls, seen, out);
  else if (ts.isUnionTypeNode(node) || ts.isIntersectionTypeNode(node)) for (const t of node.types) declaredKeys(t, decls, seen, out);
  else if (ts.isParenthesizedTypeNode(node)) declaredKeys(node.type, decls, seen, out);
}

function membersKeys(members: ts.NodeArray<ts.TypeElement>, decls: Map<string, ts.Node>, seen: Set<string>, out: Set<string>): void {
  for (const m of members)
    if (ts.isPropertySignatureDeclaration(m) && (ts.isIdentifier(m.name) || ts.isStringLiteral(m.name))) {
      out.add(m.name.text);
      declaredKeys(m.type, decls, seen, out);
    }
}

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

/** A location expression, resolved: storage allocated by the closure itself
 * (no effect on the caller's storage), or a path from a root variable of the
 * caller's scope, with every `const` alias of a path replaced by the path it
 * holds (`const ws = p.widths`: `ws` is `p.widths`); null where the path is
 * not a caller's variable's (the closure's parameter, an element, a call). */
type Resolved = { fresh: true } | { fresh: false; root: string; path: string[]; literal: boolean };

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

function resolve_(expr: ts.Expression, closure: ts.Node | null, depth: number = 0): Resolved | null {
  const e = unwrapExpr(expr);
  if (depth > 32) return null;
  if (ts.isPropertyAccessExpression(e)) {
    const base = resolve_(e.expression, closure, depth + 1);
    if (base === null) return null;
    return base.fresh ? base : { fresh: false, root: base.root, path: [...base.path, e.name.text], literal: false };
  }
  if (!ts.isIdentifier(e)) return null;
  const d = declOf(e.text, e);
  if (d === null || d.kind === "function") return null;
  const local = closure !== null && (d.kind === "param" ? d.owner === closure || within(d.owner, closure) : within(d.at, closure));
  if (d.kind === "param") return local ? null : { fresh: false, root: e.text, path: [], literal: false };
  if (d.kind === "const" && isPathExpr(d.init)) return resolve_(d.init, closure, depth + 1);
  if (local) return d.kind === "const" && isAllocation(d.init) ? { fresh: true } : null;
  return { fresh: false, root: e.text, path: [], literal: d.kind === "const" && isAllocation(d.init) };
}

/** A key's root resolved at a node: the key with its root replaced by the
 * path an alias holds, and whether its storage was allocated by a `const`
 * literal; null where the root resolves to nothing this script reads. */
function normalizeKey(key: string, at: ts.Node): { key: string; literal: boolean } | null {
  const root = rootOf(key);
  const d = declOf(root, at);
  if (d === null || d.kind === "function") return null;
  if (d.kind === "const" && isPathExpr(d.init)) {
    const inner = d.init === undefined ? null : resolveAt(d.init);
    if (inner === null) return null;
    const head = [inner.root, ...inner.path].join(".");
    return { key: head + restOf(key), literal: inner.literal };
  }
  return { key, literal: d.kind === "const" && isAllocation(d.init) };
}

function resolveAt(e: ts.Expression): { root: string; path: string[]; literal: boolean } | null {
  const r = resolve_(e, null);
  return r === null || r.fresh ? null : r;
}

/** A region key, parsed: its root, the declared keys from the root to the
location's object, and what it names there: a field, every field (`.*`),
the spine (`[*]`), or the reach through declared keys (`.**`). */
interface Loc { root: string; path: string[]; kind: "field" | "fields" | "spine" | "reach"; key: string | null }

function locOf(key: string): Loc | null {
  const m = /^([A-Za-z_$][\w$]*)((?:\.[A-Za-z_$][\w$]*)*)(\.\*\*|\.\*|\[\*\])?$/.exec(key);
  if (!m || m[1] === undefined) return null;
  const steps = (m[2] ?? "").split(".").filter((x) => x !== "");
  const tail = m[3];
  if (tail === ".**") return { root: m[1], path: steps, kind: "reach", key: null };
  if (tail === ".*") return { root: m[1], path: steps, kind: "fields", key: null };
  if (tail === "[*]") return { root: m[1], path: steps, kind: "spine", key: null };
  const last = steps.pop();
  return last === undefined ? null : { root: m[1], path: steps, kind: "field", key: last };
}

const pathText = (l: Loc): string => [l.root, ...l.path].join(".");

/** Whether two locations are disjoint, decided as the pass decides it
 * (docs/drafts/effect-languages.md, "Decisions"): a field location and a
 * spine differ (the spine's key is `[]`); two field locations at different
 * keys differ whatever objects they are on (disjointness by key); a field
 * whose key no type in a reach declares lies outside it; and storage the
 * caller allocated in its body (rule Alloc of Tolerant frames) is apart from
 * every value passed in from elsewhere. Anything else may overlap. */
function disjoint(r: Loc, b: Loc, keys: Set<string>, fresh: Set<string>): boolean {
  if (fresh.has(r.root) && r.root !== b.root && pathText(b) !== r.root) return true;
  if (b.kind === "reach") return r.kind === "field" && r.key !== null && !keys.has(r.key);
  if (r.kind === "reach") return b.kind === "field" && b.key !== null && !keys.has(b.key);
  if (r.kind === "field" && b.kind === "field") return r.key !== b.key;
  if ((r.kind === "field" && b.kind === "spine") || (r.kind === "spine" && b.kind === "field")) return true;
  return false;
}

/** Whether `r` lies in `b`: the same location, or a location reached from
 * `b`'s root through declared keys when `b` is a reach. */
function inside(r: Loc, b: Loc, keys: Set<string>): boolean {
  if (b.kind === "reach") {
    const base = pathText(b);
    const full = [r.root, ...r.path];
    const rel = pathText(r) === base ? [] : pathText(r).startsWith(base + ".") ? full.slice(base.split(".").length) : null;
    return rel !== null && rel.every((k) => keys.has(k)) && (r.kind !== "field" || (r.key !== null && keys.has(r.key))) && r.kind !== "reach";
  }
  return r.kind === b.kind && r.key === b.key && pathText(r) === pathText(b);
}

/** A closure's effect on its caller's storage, read from its body by the
 * paper's rules for steps (Section "Rules for steps"): a field write
 * `x.f = e` is `x.f: any` (Field-Write), and a compound write or an
 * increment of a field `x.f: scalar` (strict TypeScript makes its old and new
 * contents primitives); an element write `x[i] = e` is `x[*]: any`, the key
 * naming the array's spine and its cells (Elem-Write); `x.push(…)` is
 * `x[*]: extend` (Push); a call of a function declared with a result
 * `Modifies<P, T>` is `P` at its arguments (Call). Storage the closure
 * allocates is no part of it (Fresh-Eff). Any other step that may write (an
 * assignment to a captured binding, another call, `delete` of an unnamed
 * location, `new`) cannot be bounded here: the result names it. */
function closureEffect(fn: ts.ArrowFunction | ts.FunctionExpression): Effect | string {
  const entries: [string, Change][] = [];
  let otherwise: Change = "keep";
  let error: string | null = null;
  const fail = (n: ts.Node, why: string): undefined => { error ??= `the callback's ${n.getText()} ${why}`; return undefined; };
  const keyOf = (r: { root: string; path: string[] }, tail: string): string => [r.root, ...r.path].join(".") + tail;
  const write = (target: ts.Expression, change: Change, at: ts.Node): undefined => {
    const t = unwrapExpr(target);
    if (ts.isPropertyAccessExpression(t) || ts.isElementAccessExpression(t)) {
      const base = resolve_(t.expression, fn);
      if (base === null) return fail(at, "writes a location no key of the instance can name");
      if (base.fresh) return undefined;
      if (ts.isPropertyAccessExpression(t)) entries.push([keyOf(base, "." + t.name.text), change]);
      else entries.push([keyOf(base, "[*]"), "any"]);
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
      write(n.left, n.operatorToken.kind === ts.SyntaxKind.EqualsToken ? "any" : "scalar", n);
    else if ((ts.isPrefixUnaryExpression(n) || ts.isPostfixUnaryExpression(n)) &&
        (n.operator === ts.SyntaxKind.PlusPlusToken || n.operator === ts.SyntaxKind.MinusMinusToken))
      write(n.operand, "scalar", n);
    else if (ts.isDeleteExpression(n)) write(n.expression, "any", n);
    else if (ts.isNewExpression(n)) return fail(n, "constructs an object, whose effect is unknown");
    else if (ts.isCallExpression(n)) {
      const callee = unwrapExpr(n.expression);
      if (ts.isPropertyAccessExpression(callee) && callee.name.text === "push") {
        const base = resolve_(callee.expression, fn);
        if (base === null) return fail(n, "pushes onto an array no key of the instance can name");
        if (!base.fresh) entries.push([keyOf(base, "[*]"), "extend"]);
      } else if (ts.isIdentifier(callee)) {
        const d = declOf(callee.text, callee);
        const result = d?.kind === "function" ? d.node.type : undefined;
        const stated = result && ts.isTypeReferenceNode(result) && ts.isIdentifier(result.typeName) &&
          result.typeName.text === "Modifies" ? result.typeArguments?.[0] : undefined;
        const eff = stated ? effectOf(stated) : null;
        if (d?.kind !== "function" || eff === null) return fail(n, "calls a function whose effect is not stated");
        const params = d.node.parameters.map((q) => ts.isIdentifier(q.name) ? q.name.text : "");
        for (const [k, c] of eff.entries) {
          const at = params.indexOf(rootOf(k));
          const arg = n.arguments[at];
          const base = arg === undefined ? null : resolve_(arg, fn);
          if (base === null) return fail(n, `passes to ${rootOf(k)} a value no key of the instance can name`);
          if (!base.fresh) entries.push([keyOf(base, restOf(k)), c]);
        }
        if (!le(eff.else, otherwise)) otherwise = eff.else;
      } else return fail(n, "calls a method whose effect is not stated");
    }
    n.forEachChild(visit);
    return undefined;
  };
  visit(fn.body);
  return error ?? { entries, else: otherwise };
}

/** Whether a claim's location covers an effect's location: the same
 * location, a field among the fields `x.*`, or a location in the reach
 * `x.**` through declared keys. */
function covers(c: Loc, r: Loc, keys: Set<string>): boolean {
  if (c.kind === "reach") return inside(r, c, keys);
  if (c.kind === "fields") return r.kind === "field" && pathText(r) === pathText(c);
  return r.kind === c.kind && r.key === c.key && pathText(r) === pathText(c);
}

/** **The argument's type at Inst**: the closure's effect is included in the
 * written instance by the paper's order, each entry of the effect within a
 * claim entry covering it or within the claim's `else`. */
function effectWithin(eff: Effect, claim: Effect, keysOf: (root: string) => Set<string>): string | null {
  for (const [k, c] of eff.entries) {
    const r = locOf(k);
    if (!r) return `the callback changes ${k}, which no key of the instance can name`;
    const ok = claim.entries.some(([ck, d]) => {
      const l = locOf(ck);
      return l !== null && covers(l, r, keysOf(l.root)) && le(c, d);
    }) || le(c, claim.else);
    if (!ok) return `the callback changes ${k} by ${c}; the instance allows ${claim.entries.map(([ck, d]) => `${ck}: ${d}`).join(", ") || "nothing"}${claim.else === "keep" ? "" : `, else ${claim.else}`}`;
  }
  return le(eff.else, claim.else) ? null : `the callback's else ${eff.else} exceeds the instance's else ${claim.else}`;
}

/** **Rule Inst**, the paper's order (Definition "Order"): the instance is
 * included in the bound at the actual arguments when, for every bound entry
 * `b : d`, every instance entry not disjoint from `b` is within `d`, and,
 * where the bound's `else` is not `any`, every instance entry lying in no
 * bound entry, and the instance's `else`, are within that `else`. A key this
 * check cannot parse is refused. */
function instCheck(instance: Effect, bound: Effect, params: string[], args: string[], fresh: Set<string>): string | null {
  const actual = (key: string): string => {
    const at = params.indexOf(rootOf(key));
    return at < 0 ? key : (args[at] ?? "?") + restOf(key);
  };
  const keys = new Set(bound.reachKeys ?? []);
  const bs: [Loc, Change, string][] = [];
  for (const [b, d] of bound.entries) {
    const text = actual(b);
    const l = locOf(text);
    if (!l || text.startsWith("?")) return `the bound's entry ${b} is not read at this call's arguments`;
    bs.push([l, d, text]);
  }
  for (const [r, c] of instance.entries) {
    const l = locOf(r);
    if (!l) return `the instance's key ${r} is not decided`;
    for (const [b, d, text] of bs)
      if (!disjoint(l, b, keys, fresh) && !le(c, d)) return `the instance changes ${r} by ${c}; the bound allows ${text}: ${d}`;
    if (bound.else !== "any" && !bs.some(([b]) => inside(l, b, keys)) && !le(c, bound.else))
      return `the instance changes ${r} by ${c}; the bound's else allows ${bound.else}`;
  }
  for (const [, d, text] of bs)
    if (!le(instance.else, d)) return `the instance's else ${instance.else} exceeds the bound's ${text}: ${d}`;
  if (!le(instance.else, bound.else)) return `the instance's else ${instance.else} exceeds the bound's else ${bound.else}`;
  return null;
}

export function annotations(path: string): { functions: Record<string, FunctionInfo>; calls: CallInfo[] } {
  const tree = openText(path, readFileSync(path, "utf8"));
  const functions: Record<string, FunctionInfo> = {};
  const bodies = new Map<string, ts.Node>();
  const decls = new Map<string, ts.Node>();
  for (const s of tree.statements)
    if ((ts.isTypeAliasDeclaration(s) || ts.isInterfaceDeclaration(s))) decls.set(s.name.text, s);
  for (const s of tree.statements) {
    if (!ts.isFunctionDeclaration(s) || !s.name || !s.body) continue;
    bodies.set(s.name.text, s.body);
    const effectParams: EffectParam[] = [];
    for (const tp of s.typeParameters ?? []) {
      const c = tp.constraint;
      if (c && ts.isTypeReferenceNode(c) && ts.isIdentifier(c.typeName) && c.typeName.text === "AtMost") {
        const arg = c.typeArguments?.[0];
        const bound = arg ? effectOf(arg) : null;
        if (bound) effectParams.push({ name: tp.name.text, bound });
      }
    }
    const params = s.parameters.map((p) => ts.isIdentifier(p.name) ? p.name.text : "");
    for (const e of effectParams) {
      const reach = e.bound.entries.filter(([k]) => k.endsWith(".**")).map(([k]) => rootOf(k));
      if (reach.length === 0) continue;
      const out = new Set<string>();
      for (const root of reach) declaredKeys(s.parameters[params.indexOf(root)]?.type, decls, new Set(), out);
      e.bound.reachKeys = [...out].sort();
    }
    const bounded: FunctionInfo["bounded"] = [];
    s.parameters.forEach((p, index) => {
      const seen = new Set<string>();
      if (p.type) mentions(p.type, seen);
      for (const e of effectParams) if (seen.has(e.name)) bounded.push({ param: params[index] ?? "", index, variable: e.name });
    });
    functions[s.name.text] = { params, effectParams, bounded };
  }
  const calls: CallInfo[] = [];
  for (const [caller, body] of bodies) {
    const visit = (n: ts.Node): undefined => {
      if (ts.isCallExpression(n) && ts.isIdentifier(n.expression) && n.typeArguments) {
        const callee = functions[n.expression.text];
        if (callee && callee.effectParams.length > 0) {
          const instance: Record<string, Effect> = {};
          callee.effectParams.forEach((e, i) => {
            const arg = n.typeArguments?.[i];
            const eff = arg ? effectOf(arg) : null;
            if (eff) instance[e.name] = eff;
          });
          const args = n.arguments.map((a) => ts.isIdentifier(a) || ts.isPropertyAccessExpression(a) ? a.getText() : "?");
          let reason: string | null = null;
          for (const e of callee.effectParams) {
            const written = instance[e.name];
            if (written === undefined) { reason = `no instance written for ${e.name}`; break; }
            // The instance's roots resolved at the call: aliases replaced by
            // the paths they hold, and the caller's literal allocations.
            const fresh = new Set<string>();
            const entries: [string, Change][] = [];
            for (const [k, c] of written.entries) {
              const norm = normalizeKey(k, n);
              if (norm === null) { reason = `the instance's key ${k} names no variable of the caller`; break; }
              if (norm.literal) fresh.add(rootOf(norm.key));
              entries.push([norm.key, c]);
            }
            if (reason !== null) break;
            const inst: Effect = { entries, else: written.else };
            const keysOf = (root: string): Set<string> => {
              const d = declOf(root, n);
              const out = new Set<string>();
              if (d !== null && d.kind !== "function") declaredKeys(d.type, decls, new Set(), out);
              return out;
            };
            for (const b of callee.bounded.filter((x) => x.variable === e.name)) {
              let arg: ts.Expression | undefined = n.arguments[b.index];
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
              reason = typeof eff === "string" ? eff : effectWithin(eff, inst, keysOf);
              if (reason !== null) break;
            }
            if (reason !== null) break;
            reason = instCheck(inst, e.bound, callee.params, args, fresh);
            if (reason !== null) break;
          }
          calls.push({ caller, callee: n.expression.text, instance, ok: reason === null, reason });
        }
      }
      n.forEachChild(visit);
      return undefined;
    };
    visit(body);
  }
  closeParser();
  return { functions, calls };
}

if (process.argv[1] && resolve(process.argv[1]) === import.meta.filename) {
  const file = process.argv[2];
  if (file === undefined) {
    process.stderr.write("usage: node dev/paper-annotations.mts file.ts\n");
    process.exitCode = 2;
  } else process.stdout.write(JSON.stringify(annotations(resolve(file)), null, 2) + "\n");
}
