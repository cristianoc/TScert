/** Regular expressions as the model reads them (SOURCE-CONTRACTS.md,
 * "Regular expressions"): the types a literal's shape gives, and the reading
 * of the standard library's `RegExp` and match-array interfaces.
 *
 * - A literal `/P/F` is a call of `%RegExp:Σ%`, a native regex of its shape
 *   Σ (`regexp-shape.mts`): `nativeRegExp(Σ)`.
 * - An annotation `RegExp` is the conservative structural type
 *   `structuralRegExp`, every capture `string | undefined`.
 * - Both are records of host-relative methods: `exec`, `test` and the
 *   well-known-symbol methods `String.prototype`'s `match`, `matchAll`,
 *   `replace`, `search` and `split` dispatch to. No property is stated (a
 *   regex's `lastIndex`, `source` and flags are read through no type), so a
 *   regex meets no record view stating one.
 * - A native regex also states `[⟨RegExpMatcher⟩]: undefined`, keyed by a
 *   symbol only this module names (`marks`): the model's reading of the
 *   `[[RegExpMatcher]]` slot a native regex has. Only `%RegExp:Σ%` returns a
 *   value whose type states it, and `String.prototype.matchAll` requires it,
 *   where ECMA-262 reads `Symbol.match` and `flags` and converts `flags`
 *   before dispatching. Its `[Symbol.matchAll]` returns a native match
 *   iterator, marked by `[⟨RegExpStringIterator⟩]`, which the host iteration
 *   intrinsic `%Iterate:RegExpString%` requires. */
import type { DeclarationIdentity, TypeDefinition, TypeTerm } from "./declaration-types.mts";
import type { RegExpShape } from "./regexp-shape.mts";
import { closedFootprints, emptyEffect, footprintEffect, ordinaryEffect } from "./type-graph.mts";

type AtomName = Extract<TypeTerm, { k: "atom" }>["name"];
type Signature = Extract<TypeTerm, { k: "function" }>;
type Field = Extract<TypeTerm, { k: "object" }>["fields"][number];
const span: [number, number] = [0, 0];
const atom = (name: AtomName): TypeTerm => ({ k: "atom", name, span });
const either = (...parts: TypeTerm[]): TypeTerm => ({ k: "union", parts, span });
const maybeString = either(atom("string"), atom("undefined"));
const record = (fields: Field[]): TypeTerm => ({ k: "object", fields, stringIndex: null, calls: [], span });
const readonlyField = (name: Field["name"], type: TypeTerm): Field =>
  ({ name, optional: false, readonly: true, type, span });
type Effect = Signature["effect"];
const method = (params: TypeTerm[], result: TypeTerm, effect: Effect): Signature =>
  ({ k: "function", effect, receiver: { k: "self", span }, params, rest: null, result, span });
const methodField = (name: Field["name"], params: TypeTerm[], result: TypeTerm,
    effect: Effect = ordinaryEffect): Field =>
  ({ name, optional: false, readonly: false, type: method(params, result, effect), span });

/** The synthetic symbols the marks are keyed by: no source declaration has
 * these identities, so no source type, literal or class states them. */
export const marks = {
  matcher: { module: "tscert/regexp", name: "RegExpMatcher", span } satisfies DeclarationIdentity,
  stringIterator: { module: "tscert/regexp", name: "RegExpStringIterator", span } satisfies DeclarationIdentity,
};

/** The symbols the types are keyed by, by their index among the document's
 * symbols, and the library's `Iterator<T>`. */
export type RegExpKeys = {
  match: number; matchAll: number; replace: number; search: number; split: number;
  matcher: number; stringIterator: number;
  iterator: (element: TypeTerm) => TypeTerm;
};

/** A match of `exec`, of a non-global `match` and of `matchAll`: a fresh
 * array, the whole match first, then each capture, a string where the shape
 * says the group always takes part and else `string | undefined`, with the
 * match's `index`, its `input` and its `groups`: an object of the named
 * groups (each `string | undefined`), or `undefined` where none is named.
 * A readonly view, so a refined match meets the conservative one. */
export function execResult(shape: RegExpShape | null): TypeTerm {
  const captures: TypeTerm[] = shape ? shape.always.map(a => a ? atom("string") : maybeString) : [];
  const tuple: TypeTerm = { k: "tuple", presence: "dense", readonly: true, required: [atom("string"), ...captures],
    optional: [], rest: shape ? null : maybeString, span };
  const dictionary: TypeTerm = { k: "object", fields: [], calls: [], span,
    stringIndex: { readonly: true, value: maybeString, span } };
  const groups = shape === null ? either(dictionary, atom("undefined")) : shape.named ? dictionary : atom("undefined");
  return { k: "intersection", span, parts: [tuple, record([readonlyField("index", atom("number")),
    readonlyField("input", atom("string")), readonlyField("groups", groups)])] };
}

/** A `match` of the regex: a global one's every whole match (a fresh array of
 * strings, at least one, owning no `index`); a non-global one's `exec`
 * result. The conservative form covers both. */
function matchResult(shape: RegExpShape | null): TypeTerm {
  if (shape === null)
    return { k: "tuple", presence: "dense", readonly: true, required: [atom("string")], optional: [], rest: maybeString, span };
  return shape.global
    ? { k: "tuple", presence: "dense", readonly: true, required: [atom("string")], optional: [], rest: atom("string"), span }
    : execResult(shape);
}

/** `split`'s result: a fresh array of the pieces with the captures spliced
 * in, so `string | undefined` unless every group always takes part. A
 * literal's is writable; the conservative one a readonly view, which both
 * writable forms meet. */
function splitResult(shape: RegExpShape | null): TypeTerm {
  const element = shape && shape.always.every(Boolean) ? atom("string") : maybeString;
  return { k: "array", presence: "dense", readonly: shape === null, element, span };
}

/** The members of a regex of `shape` (`null`: the conservative shape). A
 * native one's `[Symbol.matchAll]` gives the native iterator; the structural
 * type states no `[Symbol.matchAll]`, which `matchAll` reaches only on a
 * native regex.
 *
 * A native regex's standard members run no client code: each reads the
 * regex's pattern, flags and `lastIndex` (a number by its contract),
 * allocates only its result, and writes `lastIndex` only where the regex is
 * global or sticky. Their `exec` and `test` take `undefined` too, as the
 * string `"undefined"`. `[Symbol.search]` restores the `lastIndex` it saved,
 * `[Symbol.split]` and `[Symbol.matchAll]` step a fresh clone: the empty
 * footprint. `exec`, `test`, `[Symbol.match]` and `[Symbol.replace]` (at a
 * string replacement) state the empty footprint where the regex is neither
 * global nor sticky, and where it is, `{value: any, store: keep}`: they
 * leave `lastIndex`, a location holding a number, where the last match
 * ended (0 after the last). The conservative shape, whose flags are not
 * read, and a structural regex's members are any value's and state none
 * (SOURCE-CONTRACTS.md, "Native footprints"). */
function members(shape: RegExpShape | null, keys: RegExpKeys, native: boolean): Field[] {
  const exec = execResult(shape);
  const optionalNumber = either(atom("number"), atom("undefined"));
  const restoring: Effect = native && shape !== null ? emptyEffect : ordinaryEffect;
  const stateless: Effect = !native || shape === null ? ordinaryEffect
    : shape.global || shape.sticky ? footprintEffect({ value: "any", store: "keep" }) : emptyEffect;
  // A native `exec` and `test` convert their argument by `ToString`, which
  // runs no code on `undefined` (`"undefined"`): stated there too. A
  // structural regex's keep their declared parameter.
  const input = native ? either(atom("string"), atom("undefined")) : atom("string");
  return [
    methodField("exec", [input], either(exec, atom("null")), stateless),
    methodField("test", [input], atom("boolean"), stateless),
    methodField({ symbol: keys.match }, [atom("string")], either(matchResult(shape), atom("null")), stateless),
    methodField({ symbol: keys.replace }, [atom("string"), atom("string")], atom("string"), stateless),
    methodField({ symbol: keys.search }, [atom("string")], atom("number"), restoring),
    methodField({ symbol: keys.split }, [atom("string"), optionalNumber], splitResult(shape), restoring),
    ...(native ? [methodField({ symbol: keys.matchAll }, [atom("string")], nativeIterator(exec), restoring)] : []),
  ];
}

/** The declaration of the native match iterator, `RegExpStringIterator<T>`:
 * the library's `Iterator<T>`, marked as the one
 * `%RegExpStringIteratorPrototype%` gives. A declaration of its own, so a
 * call's instance of `T` is read off the reference. */
export const nativeIteratorIdentity: DeclarationIdentity =
  { module: "tscert/regexp", name: "NativeRegExpStringIterator", span };
export function nativeIteratorDefinition(keys: Pick<RegExpKeys, "stringIterator" | "iterator">): TypeDefinition {
  return { declaration: nativeIteratorIdentity, bases: [],
    parameters: [{ name: "T", span, defaulted: false }],
    expression: { k: "intersection", span, parts: [keys.iterator({ k: "parameter", index: 0, span }),
      record([readonlyField({ symbol: keys.stringIterator }, atom("undefined"))])] } };
}

/** The native match iterator over `element`. */
export function nativeIterator(element: TypeTerm): TypeTerm {
  return { k: "reference", args: [element], span, reference: { name: nativeIteratorIdentity.name, span,
    arguments: [span], target: nativeIteratorIdentity } };
}

/** `N(Σ)`: what a literal of shape Σ evaluates to. */
export function nativeRegExp(shape: RegExpShape | null, keys: RegExpKeys): TypeTerm {
  return record([...members(shape, keys, true), readonlyField({ symbol: keys.matcher }, atom("undefined"))]);
}

/** `R(Σ⊤)`: what an annotation `RegExp` states. */
export function structuralRegExp(keys: RegExpKeys): TypeTerm {
  return record(members(null, keys, false));
}

const binder = (name: string): TypeTerm => ({ k: "binder", name, span });

/** The `String.prototype` methods that dispatch to their argument's
 * well-known-symbol method. */
export const dispatchMethods = ["match", "matchAll", "replace", "replaceAll", "search", "split"] as const;
export type DispatchMethod = typeof dispatchMethods[number];
export const isDispatchMethod = (name: string): name is DispatchMethod =>
  dispatchMethods.some(m => m === name);
export const dispatchName = (method: DispatchMethod): string => `%Dispatch:${method}%`;

/** `s.m(o, …rest)`, for `String.prototype`'s method `m` and an object `o`,
 * as the intrinsic `%Dispatch:m%(s, o, …rest)`: ECMA-262 requires `s`
 * coercible, runs `GetMethod(o, @@m)` and returns that method's result,
 * called on `o` with `s` and `rest`. Each is parametric in what the member
 * returns or takes, so the regex's own member decides the result. `matchAll`
 * and `replaceAll` first read `o[@@match]` and `o.flags` and convert
 * `flags`, which only a native regex's standard members make free of client
 * code: their argument must be marked native (and they throw a `TypeError`
 * for a non-global one, an outcome). Evaluation is as written: `s`, `o`,
 * then `rest`. Beside the member's call, the dispatch reads `o`'s members
 * and converts only strings: it runs no other code and writes nothing, so
 * at an `o` whose member states a closed footprint it states the same one:
 * one signature per closed footprint, each after those within it, the last
 * taking any `o`. */
export function dispatchIntrinsic(method: DispatchMethod, keys: RegExpKeys):
    { name: string; typeParams: { name: string; bound: null; resolution: null }[]; type: TypeTerm } {
  const native = method === "matchAll" || method === "replaceAll";
  const mark = native ? [readonlyField({ symbol: keys.matcher }, atom("undefined"))] : [];
  const limit = either(atom("number"), atom("undefined"));
  const x = binder("X");
  const [key, memberParams, rest, result]: [number, TypeTerm[], TypeTerm[], TypeTerm] =
    method === "match" ? [keys.match, [atom("string")], [], x]
    : method === "matchAll" ? [keys.matchAll, [atom("string")], [], x]
    : method === "search" ? [keys.search, [atom("string")], [], x]
    : method === "split" ? [keys.split, [atom("string"), limit], [limit], x]
    : [keys.replace, [atom("string"), x], [x], atom("string")];
  const memberResult = method === "replace" || method === "replaceAll" ? atom("string") : x;
  const signature = (effect: Effect): Signature => ({ k: "function", effect, receiver: null,
    params: [atom("string"), record([methodField({ symbol: key }, memberParams, memberResult, effect), ...mark]),
      ...rest], rest: null, result, span });
  return { name: dispatchName(method), typeParams: [{ name: "X", bound: null, resolution: null }],
    type: { k: "intersection", parts: closedFootprints.map((f) => signature(footprintEffect(f))), span } };
}

/** The standard library's regex interfaces, as an annotation or a contextual
 * type names them: `RegExp` the conservative structural regex,
 * `RegExpExecArray` and `RegExpMatchArray` the conservative match views, a
 * supertype of each declaration with its element type corrected (TypeScript
 * types every capture `string`). `null` for another name. */
export function libraryRegExpTerm(name: string, keys: () => RegExpKeys): TypeTerm | null {
  return name === "RegExp" ? structuralRegExp(keys())
    : name === "RegExpExecArray" ? execResult(null)
    : name === "RegExpMatchArray" ? matchResult(null)
    : null;
}

/** The intrinsic a literal of `shape` is a call of: one per shape, since the
 * type depends on nothing else. */
export function regexpIntrinsicName(shape: RegExpShape | null): string {
  if (shape === null) return "%RegExp%";
  const groups = shape.always.map(a => a ? "1" : "0").join("");
  return `%RegExp:${groups}${shape.named ? ":named" : ""}${shape.global ? ":g" : ""}${shape.sticky ? ":y" : ""}%`;
}

/** The declarations of the library's regex interfaces, as reviewed: the
 * members `structuralRegExp` states, each with its declaration's text. A
 * library declaring any of them otherwise is refused. */
export const reviewedRegExpMembers: readonly { name: string; text: string }[] = [
  { name: "exec", text: "exec(string: string): RegExpExecArray | null;" },
  { name: "test", text: "test(string: string): boolean;" },
  { name: "[Symbol.match]", text: "[Symbol.match](string: string): RegExpMatchArray | null;" },
  { name: "[Symbol.replace]", text: "[Symbol.replace](string: string, replaceValue: string): string;" },
  { name: "[Symbol.search]", text: "[Symbol.search](string: string): number;" },
  { name: "[Symbol.split]", text: "[Symbol.split](string: string, limit?: number): string[];" },];
