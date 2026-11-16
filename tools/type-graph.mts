/** Exact native type graph. Mirrors PositiveNormalization.Clause / RequestJson.
 * Row indices are references, never unfolded trees; cycles need no special case.
 * A row and a label list both denote unions. Contracts within one clause are
 * simultaneous requirements (including all arrows of an overload).
 */
import type { CallEffect, CallPromise, ClosedFootprint, ElementKind, ElementKinds, ElementWrite, ExactElementWrite, Exits, ExitSchema, Formula, Frame, IndexFact, LinearTerm, OperationPost, PropertyKey, Selector, TransportSchema, WitnessSeq } from "./declaration-types.mts";
import { requireWellFormed } from "./wire-strings.mts";
import {
  hasExactly,
  isJsonList,
  isJsonObject,
  type Json,
  type JsonObject,
  type JsonRead,
  type JsonValue,
} from "./calculus.mts";
export type { CallEffect, CallPromise, ClosedFootprint } from "./declaration-types.mts";
/** Physical density and a safe in-bounds read are distinct guarantees. */
export type ArrayPresence = "dense" | "readable" | "sparse";

/** The wire's order of strings, a string set's (HOST-FAMILIES.md, "Tag
 * sets"): lexicographic by Unicode code point, as Lean's `String` order
 * is. JavaScript's `<` compares UTF-16 code
 * units, which orders a code point past U+FFFF below one in U+E000–U+FFFF. */
export function codePointLess(a: string, b: string): boolean {
  const xs = [...a], ys = [...b];
  for (let i = 0; i < Math.min(xs.length, ys.length); i++) {
    const x = xs[i]?.codePointAt(0) ?? 0, y = ys[i]?.codePointAt(0) ?? 0;
    if (x !== y) return x < y;
  }
  return xs.length < ys.length;
}
export function isArrayPresence(value: unknown): value is Modifies<{}, ArrayPresence> {
  return value === "dense" || value === "readable" || value === "sparse";
}
export function presencePrefix(value: ArrayPresence): Modifies<{}, string> {
  return value === "readable" ? "" : `${value} `;
}
/** A union of labels. A table's labels are its row indices; each row type
 * below is generic in its label. */
export type Labels<L = number> = L[];
/** A signature: the receiver a call may pass, then the parameters and the
 * result. A signature indifferent to its receiver names an unknown row. */
/** The footprint letting every location change: an ordinary arrow's. */
export const topFootprint: ClosedFootprint = { value: "any", spine: "any" };
/** The footprint letting no location change: heap preservation. */
export const emptyFootprint: ClosedFootprint = { value: "keep", spine: "keep" };
/** The six closed footprints, each after every one within it. */
export const closedFootprints: readonly ClosedFootprint[] = [
  { value: "keep", spine: "keep" }, { value: "any", spine: "keep" },
  { value: "keep", spine: "grow" }, { value: "any", spine: "grow" },
  { value: "keep", spine: "any" }, { value: "any", spine: "any" },
];
/** A spine region of a written frame: the spine the value at the call
 * position `position` (`0` the receiver) selects through the fields `path`
 * at the call's entry (`Footprints.ArgumentSpineRegion`). */
export type SpineRegion = { readonly position: number; readonly path: readonly string[] };
/** A written statement's frame (`Modifies<P, T>`, `Fresh<T>`,
 * SOURCE-ELABORATION.md, "Stated effects"), an authoring form: its closed
 * footprint, off the spines its `regions` select, which may change
 * arbitrarily; whether it holds on a throw; whether the result is fresh.
 * The Fragment states its exits (`statedExits`). */
export type StatedFrame = { footprint: ClosedFootprint; onThrow: boolean; fresh: boolean; regions: SpineRegion[] };
/** The guarantees a footprint's signature states beside its footprint, an
 * authoring form of an effect (`footprintEffect` builds the effect): its
 * promise, whether its footprint also bounds a throw (`onThrow`), whether
 * its result's array spine or every field of its result is fresh,
 * whether it excepts its receiver's spine or fields, whether it
 * grows its receiver's spine and appends its actuals, its precondition on
 * the receiver's elements and its elements promise, its preconditions and
 * the facts a normal return states, and its element write. Never
 * serialized. */
export type EffectOptions = {
  readonly promise?: CallPromise | null;
  readonly onThrow?: boolean;
  readonly fresh?: boolean;
  readonly freshObject?: boolean;
  readonly receiverSpine?: boolean;
  readonly receiverFields?: boolean;
  readonly receiverGrows?: boolean;
  readonly requires?: ElementKinds | null;
  readonly elements?: ElementKinds | null;
  readonly pre?: readonly IndexFact[];
  readonly ensures?: readonly IndexFact[];
  readonly elementWrite?: ElementWrite | null;
};
/** The facts an exact element write's precondition states of the call's
 * positions (`CallEffects.ElementKind.preFacts`): the index at position 2 a
 * safe integer at least 0 and below the length of the typed array at
 * position 1, the value at position 3 a safe integer within the element
 * type's range. */
export function exactWritePre(write: ExactElementWrite): Modifies<{}, IndexFact[]> {
  const value = (slot: number): LinearTerm => ({ kind: "value", slot, path: [] });
  const le = (form: [LinearTerm, number][], bound: number): IndexFact => ({ linear: { fact: { le: { form, bound } } } });
  const range: readonly [number, number] | null = write === "exactUint8" ? [0, 255] : write === "exactUint16" ? [0, 65535]
    : write === "exactInt32" ? [-2147483648, 2147483647] : null;
  return [{ int: { slot: 2 } }, le([[value(2), -1]], 0),
    le([[value(2), 1], [{ kind: "view", slot: 1, path: [] }, -1]], -1), { int: { slot: 3 } },
    ...(range === null ? [] : [le([[value(3), -1]], -range[0]), le([[value(3), 1]], range[1])])];
}
const isExactWrite = (w: ElementWrite | null): w is ExactElementWrite =>
  w === "exactUint8" || w === "exactUint16" || w === "exactInt32" || w === "exactFloat64";
const formatOfWrite = (w: ExactElementWrite): ViewFormat =>
  w === "exactUint8" ? "uint8" : w === "exactUint16" ? "uint16" : w === "exactInt32" ? "int32" : "float64";
/** The selector of one content class (`Selector.values`, `.arrays`, `.views`). */
const valuesClass: Selector = { value: true, array: false, view: false };
const arraysClass: Selector = { value: false, array: true, view: false };
const viewsClass: Selector = { value: false, array: false, view: true };
/** **A closed footprint's frame** (`Closed.fp`): one entry per content class,
 * its spine change on both spine classes (`Closed.ofSpines`). */
export const classFrame = (c: ClosedFootprint): Modifies<{}, Frame> => [
  { region: { cls: valuesClass }, change: c.value }, { region: { cls: arraysClass }, change: c.spine },
  { region: { cls: viewsClass }, change: c.spine }];
/** The frame letting every location change: the note's `⊤`. */
export const topFrame: Frame = classFrame(topFootprint);
/** **The frame of a write through a typed array** (the note *Tolerant
 * frames*, View-Write, `{views: grow}`): the view spines grow, every other
 * location keeps its contents; the frame its transition postcondition
 * states (`writePosts`, `Kinds.ViewWrite.frame_iff`). */
export const viewWriteFrame: Frame = [
  { region: { cls: valuesClass }, change: "keep" }, { region: { cls: arraysClass }, change: "keep" },
  { region: { cls: viewsClass }, change: "grow" }];
/** **An exit's guarantee**: its frame and its postconditions (`ExitSchema`). */
export const exitSchema = (frame: Frame, ensures: readonly Formula[] = []): Modifies<{}, ExitSchema> =>
  ({ frame, ensures });
/** **An effect of its exits** (`CallEffects.Effect`), its promise and its
 * preconditions. */
export const effect = (exits: Exits<ExitSchema>,
    o?: { readonly promise?: CallPromise | null; readonly requires?: ElementKinds | null; readonly pre?: readonly IndexFact[] }):
    Modifies<{}, CallEffect> =>
  ({ exits, promise: o?.promise ?? null, requires: o?.requires ?? null, pre: [...(o?.pre ?? [])] });
/** A postcondition stating an index fact in phase `phase`, its positions
 * raised by `lift`. */
export const factPost = (phase: "before" | "after", lift: number, fact: IndexFact): Modifies<{}, Formula> =>
  ({ operation: { post: { fact: { phase, lift, fact } } } });
/** A postcondition stating the transport of names `t`. */
export const transportPost = (t: TransportSchema): Modifies<{}, Formula> => ({ transport: t });
/** A postcondition stating the append of `args` to the array at entry
 * position `x`, the exit position `exit` holding it. */
export const pushPost = (x: number, exit: number, args: WitnessSeq): Modifies<{}, Formula> =>
  ({ operation: { post: { push: { x, exit, args } } } });
const operation = (post: OperationPost): Formula => ({ operation: { post } });
/** The written result of an element write: entry position 3 read at exit
 * position 0, every other entry position `i` at `i + 1`
 * (`writtenResultSchema`). */
const writtenResult: TransportSchema = { shift: 1, overrides: [[3, { path: { root: 0, fields: [] } }]], boxed: false, stable: [] };
/** **An element write's postconditions** (`ElementWrite.schemaPosts`): the
 * views' growth; for an element assignment View-Write at the typed array's
 * format and the result the value written; for an exact write View-Write at
 * its format, the facts its precondition gives, and the result. */
function writePosts(w: ElementWrite): Modifies<{}, Formula[]> {
  const grow: Formula = { transition: { effect: [{ region: { cls: viewsClass }, change: "grow" }] } };
  if (w === "spines") return [grow];
  if (w === "assign") return [grow, operation({ viewWrite: { x: 1, i: 2, v: 3, format: null } }), transportPost(writtenResult)];
  return [grow, operation({ viewWrite: { x: 1, i: 2, v: 3, format: formatOfWrite(w) } }),
    ...exactWritePre(w).map(f => factPost("before", 0, f)), transportPost(writtenResult)];
}
/** The receiver's spine entry of a frame: its array spine at `any`. */
const receiverSpineEntry: Frame[number] = { region: { field: { x: 0, key: "[]" } }, change: "any" };
/** **A signature effect of a frame and its options**, the exits it
 * states (`Exits`): the normal frame the stated frame's entries, then the
 * receiver's fields (else its spine) at `any`; the normal
 * postconditions the fresh result spine and object, the receiver's
 * elements where the result is `true`, the facts after, the receiver's growth
 * and append, and the element write's; the exceptional exit the same frame
 * where `onThrow`, `⊤` otherwise, with no postcondition. An exact element
 * write states its range in its preconditions (`exactWritePre`); an effect
 * without it is refused. */
export const frameEffect = (stated: Frame, options?: EffectOptions): Modifies<{}, CallEffect> => {
  const elementWrite = options?.elementWrite ?? null;
  const pre = options?.pre ?? [];
  if (isExactWrite(elementWrite) && !exactWritePre(elementWrite).every(f => pre.some(g => canonicalText(g) === canonicalText(f))))
    throw Error(`an exact element write '${elementWrite}' states its range among its preconditions`);
  const receiver: Frame = options?.receiverFields
    ? [{ region: { inCls: { region: { fields: { x: 0 } }, selector: valuesClass } }, change: "any" }]
    : options?.receiverSpine ? [receiverSpineEntry] : [];
  const frame: Frame = [...stated, ...receiver];
  const elements = options?.elements ?? null;
  const ensures: Formula[] = [
    ...(options?.fresh ? [operation({ freshSpine: { x: 0 } })] : []),
    ...(options?.freshObject ? [operation({ freshObject: { x: 0 } })] : []),
    ...(elements === null ? [] : [operation({ elementsWhen: { x: 0, value: "true", y: 1, predicate: elements } })]),
    ...(options?.ensures ?? []).map(f => factPost("after", 0, f)),
    ...(options?.receiverGrows ? [{ transition: { effect: [receiverSpineEntry] } }, operation({ spineExtends: { x: 0 } }),
      pushPost(0, 1, { restFrom: { first: 1 } })] : []),
    ...(elementWrite === null ? [] : writePosts(elementWrite))];
  return effect({ normal: exitSchema(frame, ensures), exceptional: options?.onThrow ? exitSchema(frame) : exitSchema(topFrame) },
    { promise: options?.promise ?? null, requires: options?.requires ?? null, pre });
};
/** **A signature effect of a closed footprint and its options**: the
 * effect of its frame (`classFrame`, `frameEffect`). */
export const footprintEffect = (footprint: ClosedFootprint, options?: EffectOptions): Modifies<{}, CallEffect> =>
  frameEffect(classFrame(footprint), options);
/** **A statement's exits** (`Exits.ofStated`): the closed footprint's frame
 * and the spine regions at `any`, a fresh result spine where it states one,
 * and on a throw the same frame where it states `onThrow`, `⊤` otherwise. */
export const statedExits = (s: StatedFrame): Modifies<{}, Exits<ExitSchema>> => {
  const frame: Frame = [...classFrame(s.footprint),
    ...s.regions.map((r): Frame[number] => ({ region: { path: { x: r.position, fields: r.path, key: "[]" } }, change: "any" }))];
  return { normal: exitSchema(frame, s.fresh ? [operation({ freshSpine: { x: 0 } })] : []),
    exceptional: s.onThrow ? exitSchema(frame) : exitSchema(topFrame) };
};
/** An effect with a replacement promise and every other guarantee retained. */
export const withPromise = (e: CallEffect, promise: CallPromise | null): Modifies<{}, CallEffect> =>
  effect(e.exits, { promise, requires: e.requires, pre: e.pre });
/** An effect with further postconditions at one exit, every other guarantee
 * retained. */
export const withPosts = (e: CallEffect, exit: "normal" | "exceptional", posts: readonly Formula[]): Modifies<{}, CallEffect> => {
  const at = (q: ExitSchema): ExitSchema => exitSchema(q.frame, [...q.ensures, ...posts]);
  return effect(exit === "normal" ? { normal: at(e.exits.normal), exceptional: e.exits.exceptional }
    : { normal: e.exits.normal, exceptional: at(e.exits.exceptional) }, { promise: e.promise, requires: e.requires, pre: e.pre });
};
/** An effect with further preconditions and further facts a normal return
 * states (`fact after 0`), every other guarantee retained: a declaration's
 * `@requires` and `@ensures`. */
export const withConditions = (e: CallEffect, pre: readonly IndexFact[], ensures: readonly IndexFact[]):
    Modifies<{}, CallEffect> => {
  const posted = withPosts(e, "normal", ensures.map(f => factPost("after", 0, f)));
  return effect(posted.exits, { promise: posted.promise, requires: posted.requires, pre: [...posted.pre, ...pre] });
};
/** **A value's canonical text**: JSON with every object's keys in code point
 * order and every list in its order, absent fields left out; Lean writes a
 * document's objects in the same key order. */
export function canonicalText(v: unknown): Modifies<{}, string> {
  if (Array.isArray(v)) return `[${v.map(canonicalText).join(",")}]`;
  if (typeof v === "object" && v !== null) {
    const entries = Object.entries(v).filter(([, x]) => x !== undefined).sort(([a], [b]) => codePointLess(a, b) ? -1 : a === b ? 0 : 1);
    return `{${entries.map(([k, x]) => `${JSON.stringify(k)}:${canonicalText(x)}`).join(",")}}`;
  }
  const text = JSON.stringify(v);
  return text === undefined ? "null" : text;
}
/** **An effect's text**, the one serialization of an effect's syntax
 * (`canonicalText`): type identity and the comparison of effects read it. */
export const effectText = (e: CallEffect): Modifies<{}, string> => canonicalText(e);
/** **Whether two effects are the same**: the same text (`effectText`). */
export const sameEffect = (a: CallEffect, b: CallEffect): boolean => effectText(a) === effectText(b);
/** Heap preservation: no location may change, no promise. */
export const emptyEffect: CallEffect = footprintEffect(emptyFootprint);
/** An ordinary arrow's effect: every location may change, no promise. */
export const ordinaryEffect: CallEffect = footprintEffect(topFootprint);
/** A promise signature: a guard's or an assertion function's, about `param`,
 * whose code may change every location. */
export const promiseEffect = (asserts: boolean, param: number): Modifies<{}, CallEffect> =>
  footprintEffect(topFootprint, { promise: asserts ? { asserts: { param } } : { guards: { param } } });

/** **The serialized effect's grammar** (REQUEST-PROTOCOL.md, "The serialized
 * effect"), as data: a shape is a scalar, a list, a pair, a nullable value, a
 * record of exactly its fields (`atEntry` alone optional, and `true`), a
 * union of objects of one field each and of names, or a named shape. */
type Shape =
  | "nat" | "int" | "bool" | "string" | "true" | "bits" | "decimal"
  | { readonly list: Shape } | { readonly pair: readonly [Shape, Shape] } | { readonly nullable: Shape }
  | { readonly record: { readonly [field: string]: Shape }; readonly optional?: { readonly [field: string]: Shape } }
  | { readonly union: { readonly [tag: string]: Shape }; readonly names?: readonly string[] }
  | { readonly names: readonly string[] }
  | { readonly ref: string };
/** The kinds an elements predicate lists, each at most once, in this order. */
const elementKindOrder: readonly ElementKind[] =
  ["null", "undefined", "boolean", "number", "string", "bigint", "symbol", "object"];
const strings: Shape = { list: "string" };
const termShape: Shape = { record: { kind: { names: ["value", "length", "view", "strLength"] }, slot: "nat", path: strings },
  optional: { atEntry: "true" } };
const linear = (v: Shape): Shape => ({ union: { le: { record: { form: { list: { pair: [v, "int"] } }, bound: "int" } },
  ne: { record: { form: { list: { pair: [v, "int"] } }, bound: "int" } } } });
const grammar: { readonly [name: string]: Shape } = {
  selector: { record: { value: "bool", array: "bool", view: "bool" } },
  symbolKey: { record: { symbol: "nat" } },
  region: { union: {
    field: { record: { x: "nat", key: { ref: "keyOf" } } }, fields: { record: { x: "nat" } }, cells: { record: { x: "nat" } },
    cls: { ref: "selector" }, path: { record: { x: "nat", fields: strings, key: { ref: "keyOf" } } },
    pathFields: { record: { x: "nat", fields: strings } }, pathCells: { record: { x: "nat", fields: strings } },
    inCls: { record: { region: { ref: "region" }, selector: { ref: "selector" } } },
    spine: { record: { x: "nat", fields: strings } } }, names: ["all"] },
  frame: { list: { record: { region: { ref: "region" }, change: { names: ["keep", "init", "scalar", "grow", "any"] } } } },
  path: { record: { root: "nat", fields: strings } },
  literal: { union: { num: { record: { bits: "bits" } }, str: { record: { value: "string" } },
    bigint: { record: { value: "decimal" } }, sym: { record: { id: "nat" } } }, names: ["null", "undefined", "true", "false"] },
  witness: { union: { path: { ref: "path" }, literal: { ref: "literal" } } },
  seq: { union: { fixed: { record: { xs: { list: { ref: "witness" } } } }, restFrom: { record: { first: "nat" } },
    append: { record: { left: { ref: "seq" }, right: { ref: "seq" } } } } },
  transport: { record: { shift: "nat", overrides: { list: { pair: ["nat", { ref: "witness" }] } }, boxed: "bool",
    stable: { list: "nat" } } },
  stepVar: { union: { before: { record: { t: termShape } }, after: { record: { t: termShape } } } },
  bodyVariable: { union: { offset: { record: { delta: "nat" } },
    project: { record: { kind: { names: ["value", "length", "view", "strLength"] }, path: strings } },
    free: { record: { t: termShape } } }, names: ["index", "elem"] },
  clause: { union: { either: { record: { left: { ref: "clause" }, right: { ref: "clause" } } },
    le: { record: { form: { list: { pair: [{ ref: "bodyVariable" }, "int"] } }, bound: "int" } },
    ne: { record: { form: { list: { pair: [{ ref: "bodyVariable" }, "int"] } }, bound: "int" } } } },
  fact: { union: {
    index: { record: { slot: "nat" } }, length: { record: { array: "nat", length: "nat" } },
    bound: { record: { array: "nat", index: "nat", strict: "bool" } }, int: { record: { slot: "nat" } },
    pastSafe: { record: { slot: "nat" } }, linear: { record: { fact: linear(termShape) } },
    either: { record: { left: { ref: "fact" }, right: { ref: "fact" } } },
    guarded: { record: { slot: "nat", path: strings, tag: { names: ["null", "undefined", "true", "false"] }, body: { ref: "fact" } } },
    element: { record: { value: "nat", array: "nat", index: "nat" } },
    every: { record: { slot: "nat", path: strings, stop: termShape, body: { list: { ref: "clause" } } } },
    apart: { record: { slot: "nat", other: "nat" } },
    spineApart: { record: { slot: "nat", path: strings, other: "nat", otherPath: strings } } } },
  kinds: { list: { names: elementKindOrder } },
  post: { union: {
    arith: { record: { op: { names: ["add", "sub", "mul", "div", "pow", "xor", "rem", "bitAnd", "bitOr", "shl", "shr", "ushr",
      "lt", "le", "gt", "ge", "eq", "looseEq"] }, left: { ref: "witness" }, right: { ref: "witness" }, result: { ref: "path" } } },
    stringLength: { record: { string: { ref: "path" }, result: { ref: "path" } } },
    stringRead: { record: { string: { ref: "path" }, index: { ref: "witness" }, result: { ref: "path" } } },
    lengthsKept: { record: { x: "nat", exit: "nat" } }, boundedWrite: { record: { x: "nat", i: "nat", exit: "nat" } },
    push: { record: { x: "nat", exit: "nat", args: { ref: "seq" } } },
    fact: { record: { phase: { names: ["before", "after"] }, lift: "nat", fact: { ref: "fact" } } },
    freshSpine: { record: { x: "nat" } }, freshObject: { record: { x: "nat" } },
    elementsWhen: { record: { x: "nat", value: { ref: "literal" }, y: "nat", predicate: { ref: "kinds" } } },
    spineExtends: { record: { x: "nat" } },
    viewWrite: { record: { x: "nat", i: "nat", v: "nat", format: { nullable: { names: ["uint8", "uint16", "int32", "float64"] } } } } } },
  formula: { union: {
    transition: { record: { effect: { ref: "frame" } } }, operation: { record: { post: { ref: "post" } } },
    linear: { record: { fact: linear({ ref: "stepVar" }) } }, defined: { record: { v: { ref: "stepVar" } } },
    transport: { ref: "transport" }, and: { record: { left: { ref: "formula" }, right: { ref: "formula" } } } },
    names: ["truth", "falsity"] },
  exit: { record: { frame: { ref: "frame" }, ensures: { list: { ref: "formula" } } } },
  exits: { record: { normal: { ref: "exit" }, exceptional: { ref: "exit" } } },
  promise: { union: { guards: { record: { param: "nat" } }, asserts: { record: { param: "nat" } } } },
  effect: { record: { exits: { ref: "exits" }, promise: { nullable: { ref: "promise" } },
    requires: { nullable: { ref: "kinds" } }, pre: { list: { ref: "fact" } } } },
};
/** The recursive shapes: each layer of one takes a unit of the nesting
 * limit, along every path (`EffectCodec.nestingLimit`). */
const recursiveShapes: readonly string[] = ["region", "seq", "clause", "fact", "formula"];
/** The nesting a reader reads: an exit's frame and postconditions, and each
 * precondition, start from it. */
const nestingLimit = 256;
/** A canonical decimal integer: no leading zero, plus sign or negative zero. */
const canonicalDecimal = (v: string): boolean => /^(0|-?[1-9][0-9]*)$/.test(v);
/** An integer a number states exactly: below `2^53` in magnitude. */
const safeMagnitude = 2n ** 53n;
/** The first place a value differs from a shape, by its path, or `null`. A
 * key is a string or `{symbol}`; an elements predicate lists its kinds in
 * their order, each once; an integer is a safe one's number or another's
 * canonical decimal string; a record's and a union's fields are their own;
 * `depth` is the nesting left to the recursive shapes. */
function shapeError(shape: Shape, v: JsonRead, at: string, depth: number): Modifies<{}, string | null> {
  if (shape === "nat") return typeof v === "number" && Number.isSafeInteger(v) && v >= 0 ? null : `${at}: a natural number in the safe range`;
  if (shape === "int") {
    if (typeof v === "number") return Number.isSafeInteger(v) ? null : `${at}: an integer in the safe range, or its decimal string`;
    if (typeof v !== "string" || !canonicalDecimal(v)) return `${at}: an integer, a number or its canonical decimal string`;
    const i = BigInt(v);
    return (i < 0n ? -i : i) >= safeMagnitude ? null : `${at}: an integer in the safe range is a number`;
  }
  if (shape === "decimal") return typeof v === "string" && canonicalDecimal(v) ? null : `${at}: a canonical decimal integer`;
  if (shape === "bits") return typeof v === "string" && /^[0-9a-f]{16}$/.test(v) ? null : `${at}: sixteen lowercase hexadecimal digits`;
  if (shape === "bool") return typeof v === "boolean" ? null : `${at}: a Boolean`;
  if (shape === "string") return typeof v === "string" ? null : `${at}: a string`;
  if (shape === "true") return v === true ? null : `${at}: true`;
  if ("ref" in shape) {
    if (shape.ref === "keyOf") return typeof v === "string" ? null : shapeError({ ref: "symbolKey" }, v, at, depth);
    if (!Object.hasOwn(grammar, shape.ref)) return `${at}: no shape ${shape.ref}`;
    const named = grammar[shape.ref];
    if (named === undefined) return `${at}: no shape ${shape.ref}`;
    const recursive = recursiveShapes.includes(shape.ref);
    if (recursive && depth <= 0) return `${at}: nested beyond the limit`;
    const e = shapeError(named, v, at, recursive ? depth - 1 : depth);
    if (e !== null || shape.ref !== "kinds" || !isJsonList(v)) return e;
    const order = v.map(k => elementKindOrder.findIndex(o => o === k));
    return order.every((i, n) => n === 0 || (order[n - 1] ?? -1) < i) ? null : `${at}: kinds in their order, each once`;
  }
  if ("list" in shape) {
    if (!isJsonList(v)) return `${at}: a list`;
    for (let i = 0; i < v.length; i++) { const e = shapeError(shape.list, v[i], `${at}[${i}]`, depth); if (e !== null) return e; }
    return null;
  }
  if ("pair" in shape) {
    if (!isJsonList(v) || v.length !== 2) return `${at}: a pair`;
    return shapeError(shape.pair[0], v[0], `${at}[0]`, depth) ?? shapeError(shape.pair[1], v[1], `${at}[1]`, depth);
  }
  if ("nullable" in shape) return v === null ? null : shapeError(shape.nullable, v, at, depth);
  if ("record" in shape) {
    if (!isJsonObject(v)) return `${at}: an object`;
    const optional = shape.optional ?? {};
    for (const k of Object.keys(v))
      if (!Object.hasOwn(shape.record, k) && !Object.hasOwn(optional, k)) return `${at}/${k}: a field no effect has`;
    for (const [k, s] of Object.entries(shape.record)) {
      if (!Object.hasOwn(v, k)) return `${at}/${k}: a required field is missing`;
      const e = shapeError(s, v[k], `${at}/${k}`, depth);
      if (e !== null) return e;
    }
    for (const [k, s] of Object.entries(optional)) {
      if (!Object.hasOwn(v, k)) continue;
      const e = shapeError(s, v[k], `${at}/${k}`, depth);
      if (e !== null) return e;
    }
    return null;
  }
  if ("union" in shape) {
    if (typeof v === "string") return shape.names?.includes(v) ? null : `${at}: '${v}' is no constructor`;
    if (!isJsonObject(v)) return `${at}: a constructor`;
    const tags = Object.keys(v);
    const tag = tags[0];
    if (tags.length !== 1 || tag === undefined) return `${at}: a constructor is an object of one field`;
    if (!Object.hasOwn(shape.union, tag)) return `${at}/${tag}: no constructor`;
    const s = shape.union[tag];
    return s === undefined ? `${at}/${tag}: no constructor` : shapeError(s, v[tag], `${at}/${tag}`, depth);
  }
  return typeof v === "string" && shape.names.includes(v) ? null : `${at}: one of ${shape.names.join(", ")}`;
}
/** The first place a value differs from the serialized effect, or `null`. */
export const effectError = (v: JsonRead): Modifies<{}, string | null> => shapeError({ ref: "effect" }, v, "effect", nestingLimit);
/** **The effect a value states**, or `undefined` where it is not exactly the
 * serialized effect (`effectError`). */
export function decodeCallEffect(v: JsonRead): Modifies<{ values: "any"; spines: "grow" }, CallEffect | undefined> {
  if (effectError(v) !== null) return undefined;
  return v as CallEffect; // asserted: effectError checked the value field by field against the effect's grammar
}
/** One contract representation; every operand mapping must retain its effect. */
type CallContract<Receiver, Arguments, L = number> = {
  receiver: Receiver;
  arguments: Arguments;
  result: Labels<L>;
  effect: CallEffect;
};
type Arrow<L = number> = CallContract<Labels<L>, Labels<L>[], L>;
type MethodArrow<L = number> = CallContract<Record<string, never>, Labels<L>[], L>;
type MethodRestArrow<L = number> = CallContract<Record<string, never>, [Labels<L>[], Labels<L>], L>;
/** Read capabilities: one label list per named field, in the order the
 * row lists them. Fields a contract does not name are unconstrained. */
type Fields<L = number> = [name: PropertyKey, labels: Labels<L>][];
/** The role a storage position's location was allocated with: an ordinary
 * property, a binding's cell or an array's spine. */
type StorageRole = "field" | "cell" | "arraySpine";
const storageRoles: readonly StorageRole[] = ["field", "cell", "arraySpine"];
/** An object contract's storage positions: one per named field, with the
 * role its location was allocated with and its label list, in the order the
 * row lists them. */
type Stored<L = number> = [name: PropertyKey, role: StorageRole, labels: Labels<L>][];
/** An optional field: constrains its key only where the object has it, a
 * location of its role there; a readonly one is a view there. */
type OptionalField<L = number> = { key: PropertyKey; readonly: boolean; role: StorageRole; type: Labels<L> };
/** An own-key bound: the object's own keys are among `keys` (`among`), or
 * none of them is (an array owns no key its prototype provides). */
type KeyBound = { among: boolean; keys: PropertyKey[] };
/** A host-relative method member: its key, its fixed signatures
 * `[params, result]`, its variadic ones `[params, [rest, result]]`, and its
 * quantified ones, each a scheme row the member bound to its host meets, and
 * the types its host must meet for the fixed and variadic ones to hold. */
type MethodSig<L = number> = {
  key: PropertyKey;
  calls: MethodArrow<L>[];
  rests: MethodRestArrow<L>[];
  schemes: Labels<L>[];
  receivers: Labels<L>[];
};
type Tuple<L = number> = {
  required: Labels<L>[];
  optional: Labels<L>[];
  rest: Labels<L> | null;
  readonly: boolean;
  presence: ArrayPresence;
};
export type Clause<L = number> =
  | "nul"
  | "bool"
  | "undef"
  | "num"
  /** Semantic top: every value, and no operation through it. */
  | "top"
  | "source"
  | { boolLit: { value: boolean } }
  /** The double's bit pattern, decimal, as the consumer's UInt64. */
  | { numLit: { bits: string } }
  /** Strings, and one string, carried as itself. */
  | "str"
  | { strLit: { value: string } }
  /** Every bigint, and every symbol: an opaque value. */
  | "bigint"
  | "symbol"
  /** One bigint, as its integer: a JSON number of any length, which a
   * reader of this document shows and never computes with. */
  | { bigintLit: { value: number } }
  /** One symbol: the declaration document's `id`-th listed symbol, the one
   * a symbol key `{"symbol": id}` names. */
  | { symbolLit: { id: number } }
  /** A tag set (HOST-FAMILIES.md, "Tag sets"): two or more numbers by bit
   * pattern, or strings, sorted and distinct. */
  | { numIn: { bits: string[] } }
  | { strIn: { values: string[] } }
  /** `views` are read capabilities: a field read at a sound upper bound on
   * its contents, with no write permission through this contract. `optional`
   * fields constrain their key only where the object has it, as a view there
   * when readonly; `methods` are
   * host-relative members; each of `bounds` says which keys the object may
   * own; `stable` lists its stable keys (HOST-FAMILIES.md, "Stable keys").
   * Each is left out when there are none. */
  | { refs: { first: Stored<L>; rest: Stored<L>[]; views: Fields<L>; optional?: OptionalField<L>[];
      methods?: MethodSig<L>[]; bounds?: KeyBound[]; stable?: PropertyKey[] } }
  /** Readonly index views apply to every present own field their key class
   * admits; each of `cells`, a mutable index signature's, is also one every
   * such field holds exactly. Left out when there are none. */
  | {
      dict: {
        first: Stored<L>;
        rest: Stored<L>[];
        views: Fields<L>;
        indexes: IndexEntry<L>[];
        optional?: OptionalField<L>[];
        methods?: MethodSig<L>[];
        bounds?: KeyBound[];
        cells?: CellEntry<L>[];
        stable?: PropertyKey[];
      };
    }
  /** A tuple contract on an array spine: required positions, optional
   * positions, and the rest, or null when no further position may exist. */
  | { list: { first: Tuple<L>; rest: Tuple<L>[] } }
  /** An argument list under tuple contracts: what a rest parameter's type
   * says of the actuals past the fixed ones. */
  | { pack: { first: Tuple<L>; rest: Tuple<L>[] } }
  /** `variadic` signatures take actuals past their fixed parameters that, as
   * one argument list, are at the rest type, a `pack`; the field is left out
   * when there are none. */
  | { arrs: { arrows: Arrow<L>[]; variadic?: RestArrow<L>[] } }
  /** Construct signatures, each with its parameters, result and effect and
   * no receiver: what a class meets; and variadic ones, whose actuals past
   * the parameters are, as one argument list, at the rest type; the field is
   * left out when there are none. Its static fields, invariant record operands
   * as a callable's bag, `first` and `rest`, are left out when there are none. */
  | {
      ctors: {
        signatures: MethodArrow<L>[];
        variadic?: MethodRestArrow<L>[];
        first?: Stored<L>;
        rest?: Stored<L>[];
        views?: Fields<L>;
      };
    }
  | {
      callable: {
        first: Stored<L>;
        rest: Stored<L>[];
        arrows: Arrow<L>[];
        variadic?: RestArrow<L>[];
        methods?: MethodSig<L>[];
      };
    }
  /** The typed arrays of one format (Lean's `Clause.view`): values carrying
   * a view descriptor of that format, with host-relative `methods`, left
   * out when there are none. */
  | { view: { format: ViewFormat; methods?: MethodSig<L>[] } };
/** A typed array's element format (Lean's `ViewFormat`). */
export type ViewFormat = "uint8" | "uint16" | "int32" | "float64";
const viewFormats: readonly ViewFormat[] = ["uint8", "uint16", "int32", "float64"];
type RestArrow<L = number> = CallContract<Labels<L>, [Labels<L>[], Labels<L>], L>;
/** An ordinary row: a union of clauses. */
export type Row<L = number> = Clause<L>[];
/** A verifier graph's row also may be a parameter, a binder a scheme
 * quantifies or a graph's assignment gives a family, a scheme, one
 * callable meeting its signatures at every instance of its binders, or a
 * meet, a value parameter within clauses (`V & DepSafe`)
 * (`POSITIVE-TYPES.md`, "Parameter and scheme rows"). */
type ParamRow = { kind: "value" | "arguments" | "packed" | "spine"; name: string; param: number };
export type SchemeRow<L = number> = { scheme: { binders: L[]; signatures: Arrow<L>[];
  bounds?: [binder: L, bound: Labels<L>][]; variadic?: RestArrow<L>[];
  resolution?: { input: number; observation: number; result: number | null }[];
  /** A construct scheme: its signatures are construct signatures. */
  construct?: true } };
/** `also`: the further value parameters the row meets beside `meet`. */
type MeetRow = { meet: number; clauses: Row; also?: number[] };
type GraphRow = Row | ParamRow | SchemeRow | MeetRow;
export type TypeGraph = GraphRow[];

/** The clause kinds, split so that every consumer can be made to cover them. */
export type StringClause = Extract<Clause, string>;
/** The object clauses' keys, each once. */
const CLAUSE_KEYS = [
  "boolLit", "numLit", "strLit", "numIn", "strIn", "bigintLit", "symbolLit",
  "refs", "dict", "ctors", "list", "pack", "arrs", "callable", "view",
] as const;
export type ClauseKey = (typeof CLAUSE_KEYS)[number];
/** `ClauseKey` is exactly the keys of `Clause`'s object members: a key missing
 * from `CLAUSE_KEYS`, or one no member has, does not compile. `keyof` over a
 * union intersects, so the key extraction distributes. */
type KeysOf<T> = T extends unknown ? keyof T : never;
type Covers<Missing extends never> = Missing;
type EveryClauseKey = Covers<Exclude<KeysOf<Exclude<Clause, string>>, ClauseKey>>;
type OnlyClauseKeys = Covers<Exclude<ClauseKey, KeysOf<Exclude<Clause, string>>>>;

/** The string clauses, each once: a clause of `Clause` missing here, or a
 * string no clause is, does not compile. With `CLAUSE_KEYS`, these are the
 * only places a clause kind is enumerated. */
const STRING_CLAUSE_KEYS = [
  "nul", "bool", "undef", "num", "str", "top", "source", "bigint", "symbol",
] as const;
type EveryStringClause = Covers<Exclude<StringClause, (typeof STRING_CLAUSE_KEYS)[number]>>;
type OnlyStringClauses = Covers<Exclude<(typeof STRING_CLAUSE_KEYS)[number], StringClause>>;

/** The number a literal's bit pattern denotes. Readers show the number; the
 * bits are its identity, not its display. */
export const numberOfBits = (bits: string): Modifies<{}, number> => {
  const view = new DataView(new ArrayBuffer(8));
  view.setBigUint64(0, BigInt(bits));
  return view.getFloat64(0);
};


function obj(v: JsonRead, keys: string[]): JsonObject {
  return objOptional(v, keys, []);
}
function objOptional(
  v: JsonRead,
  keys: string[],
  optional: string[],
): JsonObject {
  if (!isJsonObject(v) || !hasExactly(v, keys, optional))
    throw Error("unexpected type graph fields");
  return v;
}
function array(v: JsonRead): readonly JsonValue[] {
  if (!isJsonList(v)) throw Error("expected graph list");
  return v;
}
/** Each element of a list, decoded in order, as a fresh dense list. */
function each<T>(v: JsonRead, decode: (x: JsonValue) => T): T[] {
  const result: T[] = [];
  for (const x of array(v)) result.push(decode(x));
  return result;
}
/** A reference to one of `size` rows. */
function labelAt(i: JsonRead, size: number): number {
  if (typeof i !== "number" || !Number.isSafeInteger(i) || i < 0 || i >= size)
    throw Error("type graph reference out of bounds");
  return i;
}
/** A union of references to `size` rows, as a fresh list. */
export function decodeLabels(v: JsonRead, size: number): Labels {
  return array(v).map((i) => labelAt(i, size));
}
/** The keys an index signature constrains: every string key, the canonical
 * numeric ones, or every symbol key (Lean's `IndexKeys`). */
type IndexClass = "strings" | "numeric" | "symbols";
/** An index contract: its key class and the type of each present key. */
type IndexEntry<L = number> = [IndexClass, Labels<L>];
/** A writable index: its key class, the role of the locations it grants and
 * the type each present key holds exactly. */
type CellEntry<L = number> = [IndexClass, StorageRole, Labels<L>];
function isIndexClass(v: unknown): v is IndexClass {
  return v === "strings" || v === "numeric" || v === "symbols";
}
function isParamKind(v: unknown): v is ParamRow["kind"] {
  return v === "value" || v === "arguments" || v === "packed" || v === "spine";
}
/** A key as TypeScript writes it: a string plainly, a symbol by its index. */
const keyText = (name: PropertyKey): string =>
  typeof name === "string" ? name : `[symbol ${name.symbol}]`;
/** The decoders of a row, and of its clauses, whose labels `label` and
 * `labels` read: the graph's row references. */
type ClauseDecoders<L> = {
  clauses: (row: JsonRead) => Row<L>;
  row: (row: JsonRead) => Row<L> | SchemeRow<L>;
};
function clauseDecoders<L>(label: (v: JsonRead) => L, labels: (v: JsonRead) => Labels<L>): ClauseDecoders<L> {
  const labelLists = (v: JsonRead): Labels<L>[] => each(v, labels);
  const indexEntry = (v: JsonRead): IndexEntry<L> => {
    const pair = array(v);
    const keyClass = pair[0];
    if (pair.length !== 2 || !isIndexClass(keyClass))
      throw Error("expected an index key class and its type");
    return [keyClass, labels(pair[1])];
  };
  const signature = (v: JsonRead): JsonObject =>
    obj(v, ["receiver", "arguments", "result", "effect"]);
  const effect = (sig: JsonObject): CallEffect => {
    const decoded = decodeCallEffect(sig.effect);
    if (decoded === undefined) throw Error("invalid callable effect");
    return decoded;
  };
  const restArguments = (v: JsonRead): [Labels<L>[], Labels<L>] => {
    const args = array(v);
    if (args.length !== 2) throw Error("expected fixed arguments and a rest contract");
    const fixed = labelLists(args[0]);
    return [fixed, labels(args[1])];
  };
  const arrow = (v: JsonRead): Arrow<L> => {
    const sig = signature(v);
    const receiver = labels(sig.receiver);
    const e = effect(sig);
    const result = labels(sig.result);
    return { receiver, arguments: labelLists(sig.arguments), result, effect: e };
  };
  const restArrow = (v: JsonRead): RestArrow<L> => {
    const sig = signature(v);
    const receiver = labels(sig.receiver);
    const e = effect(sig);
    const result = labels(sig.result);
    return { receiver, arguments: restArguments(sig.arguments), result, effect: e };
  };
  const methodArrow = (v: JsonRead): MethodArrow<L> => {
    const sig = signature(v);
    obj(sig.receiver, []);
    const e = effect(sig);
    const result = labels(sig.result);
    return { receiver: {}, arguments: labelLists(sig.arguments), result, effect: e };
  };
  const methodRestArrow = (v: JsonRead): MethodRestArrow<L> => {
    const sig = signature(v);
    obj(sig.receiver, []);
    const e = effect(sig);
    const result = labels(sig.result);
    return { receiver: {}, arguments: restArguments(sig.arguments), result, effect: e };
  };
  const arrows = (v: JsonRead): Arrow<L>[] => each(v, arrow);
  // Left out when empty: an explicit empty list is not the canonical form.
  const variadic = (v: JsonRead): RestArrow<L>[] => {
    const sigs = array(v);
    if (!sigs.length) throw Error("an empty variadic list is written by omitting it");
    return each(sigs, restArrow);
  };
  const methodVariadic = (v: JsonRead): MethodRestArrow<L>[] => {
    const sigs = array(v);
    if (!sigs.length) throw Error("an empty variadic list is written by omitting it");
    return each(sigs, methodRestArrow);
  };
  // A key: a string, or `{"symbol": i}` for the declaration document's i-th
  // symbol.
  const key = (v: JsonRead, what: string): PropertyKey => {
    if (typeof v === "string") return v;
    const r = obj(v, ["symbol"]);
    if (typeof r.symbol !== "number" || !Number.isSafeInteger(r.symbol) || r.symbol < 0)
      throw Error(`expected ${what}`);
    return { symbol: r.symbol };
  };
  const fields = (v: JsonRead, repeated = false): Fields<L> => {
    const names = new Set<string>();
    const result: Fields<L> = [];
    for (const f of array(v)) {
      const pair = array(f);
      if (pair.length !== 2)
        throw Error("expected a field name and its labels");
      const k = key(pair[0], "a field name");
      const name = keyText(k);
      if (!repeated && names.has(name))
        throw Error("duplicate field in an object contract");
      names.add(name);
      const field: [PropertyKey, Labels<L>] = [k, labels(pair[1])];
      result.push(field);
    }
    return result;
  };
  const role = (v: JsonRead): StorageRole => {
    const r = storageRoles.find((s) => s === v);
    if (r === undefined) throw Error("expected a storage role");
    return r;
  };
  const stored = (v: JsonRead, repeated = false): Stored<L> => {
    const names = new Set<string>();
    const result: Stored<L> = [];
    for (const f of array(v)) {
      const triple = array(f);
      if (triple.length !== 3)
        throw Error("expected a field name, its role and its labels");
      const k = key(triple[0], "a field name");
      const name = keyText(k);
      if (!repeated && names.has(name))
        throw Error("duplicate field in an object contract");
      names.add(name);
      const field: [PropertyKey, StorageRole, Labels<L>] = [k, role(triple[1]), labels(triple[2])];
      result.push(field);
    }
    return result;
  };
  const storedLists = (v: JsonRead): Stored<L>[] => each(v, (f) => stored(f));
  const cellEntry = (v: JsonRead): CellEntry<L> => {
    const triple = array(v);
    const keyClass = triple[0];
    if (triple.length !== 3 || !isIndexClass(keyClass))
      throw Error("expected an index key class, its role and its type");
    return [keyClass, role(triple[1]), labels(triple[2])];
  };
  const optionalFields = (v: JsonRead): OptionalField<L>[] => {
    const names = new Set<string>();
    const result: OptionalField<L>[] = [];
    for (const f of array(v)) {
      const r = obj(f, ["key", "readonly", "role", "type"]);
      const k = key(r.key, "an optional field's key");
      const name = keyText(k);
      if (names.has(name)) throw Error("duplicate optional field in an object contract");
      names.add(name);
      const readonly = r.readonly;
      if (typeof readonly !== "boolean") throw Error("expected an optional field's readonly flag");
      result.push({ key: k, readonly, role: role(r.role), type: labels(r.type) });
    }
    return result;
  };
  const methods = (v: JsonRead): MethodSig<L>[] =>
    each(v, (m) => {
      const r = obj(m, ["key", "calls", "rests", "schemes", "receivers"]);
      const k = key(r.key, "a method key");
      const schemes = labelLists(r.schemes);
      const receivers = labelLists(r.receivers);
      const calls = each(r.calls, methodArrow);
      const rests = each(r.rests, methodRestArrow);
      return { key: k, calls, rests, schemes, receivers };
    });
  const bounds = (v: JsonRead): KeyBound[] =>
    each(v, (b) => {
      const r = obj(b, ["among", "keys"]);
      const among = r.among;
      if (typeof among !== "boolean") throw Error("invalid key bound");
      return { among, keys: each(r.keys, (k) => key(k, "a key in a bound")) };
    });
  // A record's stable keys (HOST-FAMILIES.md, "Stable keys"): a nonempty
  // list of keys, omitted when empty.
  const stableKeys = (v: JsonRead): PropertyKey[] => {
    const ks = array(v);
    if (!ks.length) throw Error("an empty stable-key list is written by omitting it");
    return each(ks, (k) => key(k, "a stable key"));
  };
  const tuple = (v: JsonRead): Tuple<L> => {
    const t = obj(v, ["required", "optional", "rest", "readonly", "presence"]);
    const presence = t.presence;
    if (!isArrayPresence(presence)) throw Error("invalid tuple density flag");
    const readonly = t.readonly;
    if (typeof readonly !== "boolean")
      throw Error("invalid tuple readonly flag");
    const required = labelLists(t.required);
    const optional = labelLists(t.optional);
    const rest = t.rest === null ? null : labels(t.rest);
    return { required, optional, rest, readonly, presence };
  };
  const tuples = (v: JsonRead): { first: Tuple<L>; rest: Tuple<L>[] } => {
    const r = obj(v, ["first", "rest"]);
    const first = tuple(r.first);
    return { first, rest: each(r.rest, tuple) };
  };
  // One decoder per clause kind. A missing key does not compile, so a new
  // clause cannot reach the decoder as a silent "unknown graph clause".
  // Keyed by the language's own union, so a clause added there and not here is
  // a type error; read only at the key of `CLAUSE_KEYS` equal to the
  // document's, so a clause this does not know, `toString` among them, is a
  // refusal rather than a silent pass.
  const decode: Record<ClauseKey, (body: JsonRead) => Clause<L>> = {
    boolLit: (b) => {
      const value = obj(b, ["value"]).value;
      if (typeof value !== "boolean")
        throw Error("invalid Boolean literal");
      return { boolLit: { value } };
    },
    // The identity is the double's bit pattern, decimal, as an unsigned 64.
    numLit: (b) => {
      const bits = obj(b, ["bits"]).bits;
      if (
        typeof bits !== "string" ||
        !/^[0-9]+$/.test(bits) ||
        BigInt(bits) > 0xffffffffffffffffn
      )
        throw Error("invalid numeric literal");
      return { numLit: { bits } };
    },
    strLit: (b) => {
      const value = obj(b, ["value"]).value;
      if (typeof value !== "string")
        throw Error("invalid string literal");
      return { strLit: { value } };
    },
    // Sorted and distinct, at least two: the one spelling of a set.
    numIn: (b) => {
      const bits = array(obj(b, ["bits"]).bits).map((x) => {
        if (typeof x !== "string" || !/^[0-9]+$/.test(x) || BigInt(x) > 0xffffffffffffffffn)
          throw Error("invalid number set");
        return x;
      });
      const numbers = bits.map((x) => BigInt(x));
      if (numbers.length < 2 || numbers.some((x, i) => i > 0 && !((numbers[i - 1] ?? x) < x)))
        throw Error("invalid number set");
      return { numIn: { bits } };
    },
    strIn: (b) => {
      const values = array(obj(b, ["values"]).values).map((x) => {
        if (typeof x !== "string") throw Error("invalid string set");
        return x;
      });
      if (values.length < 2 || values.some((x, i) => i > 0 && !codePointLess(values[i - 1] ?? x, x)))
        throw Error("invalid string set");
      return { strIn: { values } };
    },
    bigintLit: (b) => {
      const value = obj(b, ["value"]).value;
      if (typeof value !== "number" || !Number.isInteger(value))
        throw Error("invalid bigint literal");
      return { bigintLit: { value } };
    },
    symbolLit: (b) => {
      const id = obj(b, ["id"]).id;
      if (typeof id !== "number" || !Number.isSafeInteger(id) || id < 0)
        throw Error("invalid symbol identity");
      return { symbolLit: { id } };
    },
    refs: (b) => {
      const r = objOptional(b, ["first", "rest", "views"], ["optional", "methods", "bounds", "stable"]);
      // A verifier graph's record is a meet of field constraints: the
      // intersection of two records constraining one key states the key once
      // per constraint, as the views below do.
      const first = stored(r.first, true);
      const rest = storedLists(r.rest);
      // Views are conjunctive capabilities, not an object literal: a meet
      // can constrain one key more than once, exactly as Lean viewT does.
      const views = fields(r.views, true);
      const optional = "optional" in r ? optionalFields(r.optional) : undefined;
      const sigs = "methods" in r ? methods(r.methods) : undefined;
      const keyBounds = "bounds" in r ? bounds(r.bounds) : undefined;
      const stable = "stable" in r ? stableKeys(r.stable) : undefined;
      return {
        refs: {
          first, rest, views,
          ...(optional === undefined ? {} : { optional }),
          ...(sigs === undefined ? {} : { methods: sigs }),
          ...(keyBounds === undefined ? {} : { bounds: keyBounds }),
          ...(stable === undefined ? {} : { stable }),
        },
      };
    },
    dict: (b) => {
      const r = objOptional(b, ["first", "rest", "views", "indexes"], ["optional", "methods", "bounds", "cells", "stable"]);
      const first = stored(r.first);
      const rest = storedLists(r.rest);
      // Views are conjunctive capabilities, not an object literal: a meet
      // can constrain one key more than once, exactly as Lean viewT does.
      const views = fields(r.views, true);
      const indexes = each(r.indexes, indexEntry);
      const cells = "cells" in r ? each(r.cells, cellEntry) : undefined;
      const optional = "optional" in r ? optionalFields(r.optional) : undefined;
      const sigs = "methods" in r ? methods(r.methods) : undefined;
      const keyBounds = "bounds" in r ? bounds(r.bounds) : undefined;
      const stable = "stable" in r ? stableKeys(r.stable) : undefined;
      return {
        dict: {
          first, rest, views, indexes,
          ...(optional === undefined ? {} : { optional }),
          ...(sigs === undefined ? {} : { methods: sigs }),
          ...(keyBounds === undefined ? {} : { bounds: keyBounds }),
          ...(cells === undefined ? {} : { cells }),
          ...(stable === undefined ? {} : { stable }),
        },
      };
    },
    ctors: (b) => {
      const r = objOptional(b, ["signatures"], ["variadic", "first", "rest", "views"]);
      const first = "first" in r ? stored(r.first) : undefined;
      const rest = "rest" in r ? storedLists(r.rest) : undefined;
      const views = "views" in r ? fields(r.views, true) : undefined;
      const signatures = each(r.signatures, methodArrow);
      const sigs = "variadic" in r ? methodVariadic(r.variadic) : undefined;
      return {
        ctors: {
          signatures,
          ...(sigs === undefined ? {} : { variadic: sigs }),
          ...(first === undefined ? {} : { first }),
          ...(rest === undefined ? {} : { rest }),
          ...(views === undefined ? {} : { views }),
        },
      };
    },
    list: (b) => ({ list: tuples(b) }),
    pack: (b) => ({ pack: tuples(b) }),
    arrs: (b) => {
      const r = objOptional(b, ["arrows"], ["variadic"]);
      const fixed = arrows(r.arrows);
      const sigs = "variadic" in r ? variadic(r.variadic) : undefined;
      return { arrs: { arrows: fixed, ...(sigs === undefined ? {} : { variadic: sigs }) } };
    },
    callable: (b) => {
      const r = objOptional(b, ["first", "rest", "arrows"], ["variadic", "methods"]);
      const first = stored(r.first);
      const rest = storedLists(r.rest);
      const fixed = arrows(r.arrows);
      const sigs = "variadic" in r ? variadic(r.variadic) : undefined;
      const members = "methods" in r ? methods(r.methods) : undefined;
      return {
        callable: {
          first, rest, arrows: fixed,
          ...(sigs === undefined ? {} : { variadic: sigs }),
          ...(members === undefined ? {} : { methods: members }),
        },
      };
    },
    view: (b) => {
      const r = objOptional(b, ["format"], ["methods"]);
      const format = viewFormats.find((f) => f === r.format);
      if (format === undefined) throw Error("invalid typed array format");
      const members = "methods" in r ? methods(r.methods) : undefined;
      return { view: { format, ...(members === undefined ? {} : { methods: members }) } };
    },
  };

  const clauses = (row: JsonRead): Row<L> => {
    const result: Row<L> = [];
    for (const c of array(row)) {
      if (typeof c === "string") {
        const kind = STRING_CLAUSE_KEYS.find((k) => k === c);
        if (kind === undefined) throw Error("unknown graph clause");
        result.push(kind);
        continue;
      }
      if (!isJsonObject(c)) throw Error("unknown graph clause");
      // The clause's one key and its body, read from its own entries.
      const entries = Object.entries(c);
      const entry = entries[0];
      const kind = entry === undefined ? undefined : CLAUSE_KEYS.find((k) => k === entry[0]);
      if (entry === undefined || kind === undefined) throw Error("unknown graph clause");
      if (entries.length !== 1) throw Error("unexpected type graph fields");
      const decodeClause = decode[kind];
      result.push(decodeClause(entry[1]));
    }
    return result;
  };
  // A row: a scheme, or a union of clauses.
  const row = (v: JsonRead): Row<L> | SchemeRow<L> =>
    isJsonObject(v) && "scheme" in v ? scheme(obj(v, ["scheme"]).scheme) : clauses(v);
  const scheme = (v: JsonRead): SchemeRow<L> => {
    const r = objOptional(v, ["binders", "signatures"],
      ["bounds", "variadic", "resolution", "construct"]);
    if ("construct" in r && r.construct !== true) throw Error("a scheme's construct field, when present, is true");
    const binders = each(r.binders, label);
    const signatures = arrows(r.signatures);
    const binderBounds = "bounds" in r
      ? each(r.bounds, (b): [L, Labels<L>] => {
          const pair = array(b);
          if (pair.length !== 2) throw Error("expected a binder and its bound");
          const binder = label(pair[0]);
          return [binder, labels(pair[1])];
        })
      : undefined;
    const sigs = "variadic" in r ? variadic(r.variadic) : undefined;
    let resolution: { input: number; observation: number; result: number | null }[] | undefined;
    if ("resolution" in r) {
      const owned = new Set<number>();
      const slot = (s: JsonRead): number => {
        if (typeof s !== "number" || !Number.isSafeInteger(s) || s < 0 ||
            s >= binders.length || owned.has(s))
          throw Error("resolution slots must be distinct binder positions");
        owned.add(s);
        return s;
      };
      const groups: { input: number; observation: number; result: number | null }[] = [];
      for (const group of array(r.resolution)) {
        const slots = obj(group, ["input", "observation", "result"]);
        // An awaitable group has no result slot.
        const input = slot(slots.input);
        const observation = slot(slots.observation);
        const result = slots.result === null ? null : slot(slots.result);
        groups.push({ input, observation, result });
      }
      resolution = groups;
    }
    const construct = "construct" in r;
    return {
      scheme: {
        binders, signatures,
        ...(binderBounds === undefined ? {} : { bounds: binderBounds }),
        ...(sigs === undefined ? {} : { variadic: sigs }),
        ...(resolution === undefined ? {} : { resolution }),
        ...(construct ? { construct: true as const } : {}),
      },
    };
  };
  return { clauses, row };
}
/** The type graph a parsed document states, as fresh rows of the clauses it
 * checked. */
export function decodeGraph(value: Json | undefined): TypeGraph {
  requireWellFormed(value, "type graph");
  const rows = array(value);
  const label = (v: JsonRead): number => labelAt(v, rows.length);
  const labels = (v: JsonRead): Labels => decodeLabels(v, rows.length);
  const { clauses, row: schemeOrClauses } = clauseDecoders(label, labels);
  const graph: TypeGraph = [];
  rows.forEach((row, index) => {
    if (isJsonObject(row) && "meet" in row) {
      const r = objOptional(row, ["clauses", "meet"], ["also"]);
      const meet = label(r.meet);
      const also = "also" in r ? each(r.also, label) : undefined;
      graph.push({ meet, clauses: clauses(r.clauses), ...(also === undefined ? {} : { also }) });
      return;
    }
    if (isJsonObject(row) && "param" in row) {
      const r = obj(row, ["kind", "name", "param"]);
      const kind = r.kind, name = r.name;
      if (!isParamKind(kind) || typeof name !== "string" ||
          r.param !== index)
        throw Error("invalid parameter row");
      graph.push({ kind, name, param: index });
      return;
    }
    graph.push(schemeOrClauses(row));
  });
  return graph;
}
