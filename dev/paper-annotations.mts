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

/** A function's `const` locals allocated by an object or array literal and
 * never assigned: the storage it allocates in its body. */
function freshLocals(body: ts.Node): Set<string> {
  const fresh = new Set<string>();
  const assigned = new Set<string>();
  const visit = (n: ts.Node): undefined => {
    if (ts.isVariableDeclarationList(n) && (n.flags & ts.NodeFlags.Const) !== 0)
      for (const d of n.declarations)
        if (ts.isIdentifier(d.name) && d.initializer &&
            (ts.isObjectLiteralExpression(d.initializer) || ts.isArrayLiteralExpression(d.initializer)))
          fresh.add(d.name.text);
    if (ts.isBinaryExpression(n) && n.operatorToken.kind === ts.SyntaxKind.EqualsToken && ts.isIdentifier(n.left))
      assigned.add(n.left.text);
    n.forEachChild(visit);
    return undefined;
  };
  visit(body);
  for (const a of assigned) fresh.delete(a);
  return fresh;
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
    const fresh = freshLocals(body);
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
            const inst = instance[e.name];
            reason = inst ? instCheck(inst, e.bound, callee.params, args, fresh) : `no instance written for ${e.name}`;
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
