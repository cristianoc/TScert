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

/** An effect of the paper: entries in the `Modifies` key syntax, and `else`. */
interface Effect { entries: [string, Change][]; else: Change }

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

/** The check of an instance against a bound at a call (rule Inst): every
 * instance entry that meets a bound entry at the actual arguments is within
 * that entry's change, or the two are apart because the instance's root is
 * storage the caller allocated and the bound's root is another value; every
 * other entry, and the instance's `else`, are within the bound's `else`. */
function instCheck(instance: Effect, bound: Effect, params: string[], args: string[], fresh: Set<string>): string | null {
  const actual = (key: string): string => {
    const at = params.indexOf(rootOf(key));
    return at < 0 ? key : (args[at] ?? "?") + restOf(key);
  };
  for (const [r, c] of instance.entries) {
    let covered = false;
    for (const [b, d] of bound.entries) {
      const bAt = actual(b);
      const sameKind = restOf(r) === restOf(bAt);
      const apart = fresh.has(rootOf(r)) && rootOf(r) !== rootOf(bAt);
      if (!sameKind || apart) continue;
      covered = true;
      if (!le(c, d)) return `the instance changes ${r} by ${c}; the bound allows ${bAt}: ${d}`;
    }
    if (!covered && !le(c, bound.else)) return `the instance changes ${r} by ${c}; the bound's else allows ${bound.else}`;
  }
  if (!le(instance.else, bound.else)) return `the instance's else ${instance.else} exceeds the bound's else ${bound.else}`;
  return null;
}

export function annotations(path: string): { functions: Record<string, FunctionInfo>; calls: CallInfo[] } {
  const tree = openText(path, readFileSync(path, "utf8"));
  const functions: Record<string, FunctionInfo> = {};
  const bodies = new Map<string, ts.Node>();
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
          const args = n.arguments.map((a) => ts.isIdentifier(a) ? a.text : "?");
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
