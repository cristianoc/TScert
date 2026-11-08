/** The standard library's global values, such as `BigInt` and `Symbol`, as a
 * client may use them: TypeScript's own declarations, as the project's
 * standard library states them, through a reviewed overlay (SOURCE-CONTRACTS.md,
 * "Library globals"). Nothing is vendored. As for `Array.prototype`
 * (`array-prototype.mts`), the overlay holds only what those declarations do
 * not say and soundness needs:
 *
 * - which signatures exist: a global's call, construct, method or property
 *   signature is read only when an entry lists it, with exactly the text it
 *   was reviewed against, so a changed library is refused and reviewed again;
 * - where the host runs code of the client's on an argument the declaration
 *   admits (`String` of an object calls its `toString`), the parameter the
 *   reader states instead: the part of the declared type on which it runs
 *   none (`admit`). Where the host only throws on an argument (`BigInt(1.5)`,
 *   a `RangeError`), the declaration is read as it is: a throw is an outcome,
 *   never a wrong value (SOURCE-MODEL.md, "Throws");
 * - where the declaration states less than the host does (`any`) or more (a
 *   parameter at which it misbehaves), the signature the host meets, stated
 *   instead (`stated`);
 * - a member whose call is a primitive of the calculus: a test (`test`) or
 *   a trusted step already stated as an intrinsic (`intrinsic`);
 * - a call signature that holds of the global read as a value (`value`).
 *
 * A global declared outside the standard library, such as Node's `process`,
 * is read as its declaration states, member by member (`selectGlobal`). */
import { obligated, transparent, type HostClass } from "./host-operations.mts";
import type { DeclarationIdentity, LinearTerm, TypeDefinition, TypeTerm } from "./declaration-types.mts";
import type { Span } from "./span.mts";
import { asyncCompleteName, instanceOfErrorName, instanceOfMapName, instanceOfSetName, ownKeysName, promiseResolveName, prototypeIsObjectName, ownStringName, newPromiseName, promiseAllName, promiseRejectName, symbolForName,
  symbolKeyForName, typeOfDocumentName, typeOfNavigatorName, typeOfOffscreenCanvasName, urlHrefName, newSegmenterName, newDateTimeFormatName, arrayLengthName, arrayFilledName } from "./intrinsics.mts";
import { footprintEffect, emptyFootprint, emptyEffect, ordinaryEffect } from "./type-graph.mts";
import type { CallEffect } from "./type-graph.mts";
import { buffer, bytes, canvas, computedStyle, definitions as stated, documentType, element, navigatorType, textDecoder, url, viewDefinitions, viewKinds } from "./library-types.mts";

type AtomName = Extract<TypeTerm, { k: "atom" }>["name"];

/** A signature the overlay states: its binders, its parameters, the element
 * type of its rest parameter where it has one, its result. */
export type Stated = { binders: string[]; params: TypeTerm[]; rest?: TypeTerm; result: TypeTerm;
  /** The effect of this form alone, where the forms of an entry only
   * constructed state different ones (`GlobalEntry.constructs`). */
  effect?: CallEffect };
/** A standard library interface applied to arguments, such as `Set<T>`. */
type LibraryReference = (name: string, args: TypeTerm[]) => TypeTerm;
/** A host collection's reading view applied to arguments, `NativeSetView<T>`
 * (`array-prototype.mts`). */
type CollectionViewReference = (kind: "Set" | "Map", args: TypeTerm[]) => TypeTerm;

export type GlobalEntry = {
  /** The global variable, `declare var BigInt: BigIntConstructor`. */
  global: string;
  /** The member read, `Symbol.for`; absent for a call of the global itself. */
  member?: string;
  /** The declaration, exactly as reviewed. */
  signature: string;
  /** A parameter some declared arguments of which the host runs the client's
   * code on: it is stated as `safe`, the part on which it runs none. */
  admit?: { parameter: string; safe: AtomName[] };
  /** The call is a test of the calculus, not a call of the member: the
   * parser writes `Array.isArray(e)` as the test `isArray` of `e`, whose
   * narrowing Lean proves, and the member joins no value. An entry without a
   * member, whose signature is the variable's declaration, reads
   * `e instanceof X` as the test. */
  test?: "isArray";
  /** The call signature holds of the global read as a value: whoever
   * receives the value may call it with any receiver and any arguments the
   * signature admits, and the entry states what the host does at each. A
   * global is read as a value only where every call signature's entry says
   * so. */
  value?: true;
  /** The entry's signature is the variable's declaration, whose type is
   * not read: the global is only constructed, `new X(…)` read at the stated
   * forms as construct signatures. For a global whose declared type the
   * reader has no reading of (Node's `TextDecoder`, a conditional type). */
  constructs?: true;
  /** The call runs the global's construct steps: the parser writes `Error(m)`
   * as `new Error(m)`, and the call is read at `stated` as a construct
   * signature, joining the global's construct signatures. */
  construct?: true;
  /** The call is a call of this intrinsic (`intrinsics.mts`), which states
   * the same step: the parser writes `Promise.resolve(v)` as
   * `%PromiseResolve%(v)`, and the member joins no value. */
  intrinsic?: string;
  /** The call freezes its argument, admitted of a fresh object literal of
   * named fields alone: the parser writes `Object.freeze({…})` as
   * `%Freeze:K%({…})` (`freezeIntrinsic`), whose result holds the fields as
   * readonly views, and the member joins no value. */
  freezes?: true;
  /** The global is a constant of the standard library, a non-writable,
   * non-configurable data property of the global object, `Infinity`: its
   * signature is the variable's declaration, and each reference reads it as
   * a value of the stated result's type. */
  constant?: true;
  /** `typeof X` of the global, `X` a value some hosts define and others do
   * not (the DOM's `document` in a worker), is a call of this intrinsic,
   * answering the strings `typeof` answers of the value or of no binding:
   * the comparison of it with a literal narrows nothing. Every other
   * reference reads the value the host defines, and throws a
   * `ReferenceError` in a host that defines none, an outcome. */
  typeOf?: string;
  /** For a global only constructed: a read of `href` written directly on
   * the `new` expression, `new X(…).href`, is a call of this intrinsic with
   * the construct's arguments. No other code reaches the object the
   * construct makes before the read. */
  serialized?: string;
  /** For a construct signature of a length: the construct is read only as
   * the receiver of a call of the standard `fill` of one argument written
   * directly on it, `new X<T>(n).fill(v)`, which is a call of `fill` at a
   * call of `length` with `n`, and `v`. No other code reaches the object the
   * construct makes before `fill` returns it. */
  filled?: { length: string; fill: string };
  /** The member is read only in `X.m(e) === X.prototype` or `!==`, either
   * side, `X` the global at both references: the comparison is a call of
   * this intrinsic at `e` (negated for `!==`), and the member's result
   * reaches the program in no other way. */
  prototypeTest?: string;
  /** A read `?.value` of the call's result, bound to a `const` declaration
   * each reference of which is the operand of `typeof … === "string"` (or
   * `!==`, either side) or a read TypeScript types `string`, is a call of
   * this intrinsic with the call's arguments: the string the descriptor's
   * value is, `undefined` otherwise. At every such reference the two agree,
   * and no other value of the object's field reaches the program. */
  ownString?: string;
  /** Reflect.apply: invoke the target with its receiver and array-like list. */
  receiverApply?: true;
  /** The member is read only as the tag of a tagged template, never called
   * or read otherwise, and names the lowering: `"raw"`, ECMA-262's
   * `String.raw`, whose tagged template the parser writes as the template
   * of the source's raw strings (SOURCE-CONTRACTS.md, "String.raw as a
   * tag"). The member joins no value. */
  templateTag?: "raw";
  /** The signature read instead of the declared one: its own binders, its
   * parameters, which a call may not exceed, and its result. What the host
   * does at these arguments, stated as a type. For a property, its type is
   * the result. */
  stated?: Stated | ((library: LibraryReference, view: CollectionViewReference) => Stated);
  /** Several signatures read instead of the declared one, each as `stated`
   * reads one, under binders every form names alike: construct signatures,
   * or the overloads of a member, each the host's steps at the arguments it
   * states. */
  forms?: Stated[] | ((library: LibraryReference, view: CollectionViewReference) => Stated[]);
  /** Declarations the stated signature names that no library declares, such
   * as `JsonValue`: they join the document when the entry is read. */
  definitions?: TypeDefinition[];
  /** The effect the read signature states, where reviewed: a call at the
   * parameters it states runs no client code and leaves every location it
   * did not allocate as it was. Absent, the signature states none. */
  effect?: CallEffect;
  /** The entry's classification against restricted values
   * (`host-operations.mts`): required, so every entry states one; a
   * reviewed record that no check reads. */
  host: HostClass;
  /** Where the reviewed declaration comes from: the standard library
   * (`library`, the default) or the installed package of that name
   * (`@types/node`), as `declarationOrigin` resolves it. */
  origin?: string;
};

/** What `Error` constructs, what a class extending it is beside its own
 * members, and what the library's `Error` interface is read as: an object
 * whose prototype link holds its `message` and its `name`, strings, keys no
 * copy takes, as JavaScript's own non-enumerable `message` and the `name` it
 * inherits from `Error.prototype` are not copied either. */
export function errorInstance(span: Span): TypeTerm {
  const text = (name: string): Extract<TypeTerm, { k: "object" }>["fields"][number] => ({ name, optional: false, readonly: true,
    type: { k: "atom", name: "string", span }, span });
  return { k: "object", fields: [], stringIndex: null, calls: [], span,
    prototype: { k: "object", fields: [text("message"), text("name")], stringIndex: null, calls: [], span } };
}

/** The members of the library's `Error` interface, as `errorInstance`
 * reads them: `name` and `message` on the link, and `stack` and `cause`
 * unstated, so that a read of either is refused. */
export const reviewedErrorMembers: readonly string[] =
  ["name: string;", "message: string;", "stack?: string;", "cause?: unknown;"];

/** What `Error` reads of its options, `options` absent or `undefined`, or
 * an object whose `cause` its type states, at any value, or absent: ECMA-262's
 * InstallErrorCause checks `HasProperty(options, "cause")`, which looks the
 * key up along the prototype chain, and where it holds reads it by `Get`.
 * Neither runs code on such an object: no object is a proxy, a value
 * meeting a stated field holds it as a data property, and
 * `Object.prototype` owns no `cause` (DESIGN.md, the trust surface). A
 * type not stating `cause` is open at it: the object may own an accessor
 * there, whose getter `Get` would run. */
export function errorOptions(span: Span): Within<{ value: "any"; store: "grow" }, TypeTerm> {
  return { k: "union", span, parts: [{ k: "object", stringIndex: null, calls: [], span, fields: [{ name: "cause",
    optional: true, readonly: true, type: { k: "atom", name: "unknown", span }, span }] }, { k: "atom", name: "undefined", span }] };
}

const at: [number, number] = [0, 0];
const binder = (name: string): TypeTerm => ({ k: "binder", name, span: at });
const atom = (name: AtomName): TypeTerm => ({ k: "atom", name, span: at });
const optional = (type: TypeTerm): TypeTerm => ({ k: "union", parts: [type, atom("undefined")], span: at });
const readonlyArray = (element: TypeTerm): TypeTerm => ({ k: "array", presence: "readable", readonly: true, element, span: at });
const array = (element: TypeTerm): TypeTerm => ({ k: "array", presence: "readable", readonly: false, element, span: at });
/** The primitives, which ToNumber and ToString convert without running code. */
const primitive: TypeTerm = { k: "union", span: at,
  parts: [atom("null"), atom("undefined"), atom("boolean"), atom("number"), atom("string"), atom("bigint"),
    atom("symbol")] };
/** A descriptor `FromPropertyDescriptor` makes of an own property: a data
 * property's `value` and `writable` or an accessor's `get` and `set`, and
 * both kinds' `enumerable` and `configurable`. */
/** A field of an object type term. */
type Field = Extract<TypeTerm, { k: "object" }>["fields"][number];
const descriptorField = (name: string, type: TypeTerm, isOptional: boolean, readonly: boolean): Field =>
  ({ name, optional: isOptional, readonly, type, span: at });
const descriptor = (readonly: boolean): TypeTerm => ({ k: "object", stringIndex: null, calls: [], span: at, fields: [
  descriptorField("configurable", atom("boolean"), false, readonly),
  descriptorField("enumerable", atom("boolean"), false, readonly),
  descriptorField("value", atom("unknown"), true, readonly), descriptorField("writable", atom("boolean"), true, readonly),
  descriptorField("get", atom("unknown"), true, readonly), descriptorField("set", atom("unknown"), true, readonly)] });
const propertyDescriptor: TypeTerm = descriptor(true);
/** The same descriptor, its fields writable: one of the fresh descriptors
 * `Object.getOwnPropertyDescriptors` makes, which no other reference holds. */
const freshDescriptor: TypeTerm = descriptor(false);
const dictionary = (value: TypeTerm): TypeTerm =>
  ({ k: "object", fields: [], stringIndex: { readonly: true, value, span: at }, calls: [], span: at });

/** The values `JSON.stringify` serializes to a string with no code of the
 * client's run and no `undefined` returned: `null`, a Boolean, a number, a
 * string, a read-only array of such values or `undefined`, or a dictionary
 * of such values,
 *
 *     type JsonValue = null | boolean | number | string | readonly (JsonValue | undefined)[] | { readonly [k: string]: JsonValue };
 *
 * A dictionary owns no `[[proto]]` and every string key it owns holds a
 * `JsonValue` (`dictViewT`), so no key it owns is callable and it inherits
 * only what `Object.prototype` holds. An array owns no `toJSON` (the arrays'
 * own-key exclusion, `RequestJson.arrayExcludedKeys`) and inherits none: no
 * object along its prototype chain holds one, a host assumption (DESIGN.md,
 * the trust surface). So `toJSON` is never called, and no getter runs. The
 * array admits holes and explicit `undefined` elements: SerializeJSONArray
 * writes `null` when SerializeJSONProperty returns `undefined`. Neither
 * `Array.prototype` nor `Object.prototype` owns a numeric key. Root
 * `undefined` is excluded because its serialization returns `undefined`. A
 * record a declaration types by its fields is left out: a record is open,
 * and nothing bounds the own keys it does not declare. A cycle throws, an
 * outcome; a bigint would throw too, and is left out as a value the host
 * never serializes. */
const jsonValueIdentity: DeclarationIdentity = { module: "tscert/json", name: "JsonValue", span: at };
const jsonValue: TypeTerm = { k: "reference", args: [], span: at,
  reference: { name: jsonValueIdentity.name, span: at, arguments: [], target: jsonValueIdentity } };
const jsonValueDefinition: TypeDefinition = { declaration: jsonValueIdentity, parameters: [], bases: [],
  expression: { k: "union", span: at, parts: [atom("null"), atom("boolean"), atom("number"), atom("string"),
    { k: "array", presence: "readable", readonly: true,
      element: { k: "union", parts: [jsonValue, atom("undefined")], span: at }, span: at }, dictionary(jsonValue)] } };

/** What `JSON.parse` returns without a reviver: `null`, a Boolean, a number,
 * a string, an array of such values, or an object of them,
 *
 *     type ParsedJson = null | boolean | number | string | ParsedJson[] | { [k: string]: ParsedJson };
 *
 * ECMA-262's `JSON.parse` evaluates the text as a JSON value: each array it
 * builds is a fresh array (ArrayCreate) with one element at every index below
 * its length, each object a fresh ordinary object (OrdinaryObjectCreate of
 * `%Object.prototype%`) whose members it defines as own data properties
 * (CreateDataProperty, a `"__proto__"` member included, which becomes an own
 * key and sets no prototype); without a reviver, InternalizeJSONProperty
 * never runs. The array is `T[]` at writable elements, the object a writable
 * dictionary, as a client may go on writing what is fresh. Each arm is a
 * `JsonValue`'s, writable: a `ParsedJson` is a `JsonValue`. */
const parsedJsonIdentity: DeclarationIdentity = { module: "tscert/json", name: "ParsedJson", span: at };
const parsedJson: TypeTerm = { k: "reference", args: [], span: at,
  reference: { name: parsedJsonIdentity.name, span: at, arguments: [], target: parsedJsonIdentity } };
const parsedJsonDefinition: TypeDefinition = { declaration: parsedJsonIdentity, parameters: [], bases: [],
  expression: { k: "union", span: at, parts: [atom("null"), atom("boolean"), atom("number"), atom("string"),
    { k: "array", presence: "readable", readonly: false, element: parsedJson, span: at },
    { k: "object", fields: [], stringIndex: { readonly: false, value: parsedJson, span: at }, calls: [], span: at }] } };

/** An entry whose parameters are primitives or whose contract states nothing
 * of an object argument's members. */
const contract = transparent("its contract holds of any value of its parameter types");

/** A string literal type. */
const text = (value: string): TypeTerm => ({ k: "literal", name: "string", text: value, span: at });
/** The signals a listener may be registered for, and `kill` may send
 * (SOURCE-CONTRACTS.md, "Node's process"). */
const signal: TypeTerm = { k: "union", span: at, parts: ["SIGINT", "SIGTERM", "SIGHUP", "SIGUSR1", "SIGUSR2"].map(text) };
/** A listener the host calls with `argument` alone and the process as
 * `this`, whatever it runs. */
const listener = (argument: TypeTerm): TypeTerm => ({ k: "function", effect: ordinaryEffect, receiver: null,
  params: [argument], rest: null, result: atom("unknown"), span: at });
/** Node's declarations' package. */
const node = "@types/node";
/** Node's `process` (SOURCE-CONTRACTS.md, "Node's process"): the members the
 * repository's code reads, each pinned to its declaration in `@types/node`.
 * A read member is readonly: no write of `process.argv` or `process.env`
 * is admitted here. */
const processEntries: GlobalEntry[] = [
  // `process.argv`: an array of strings Node builds at start-up, read as a
  // readonly view; code replacing it or writing a non-string into it is
  // outside the assumption.
  { host: contract, origin: node, global: "process", member: "argv", signature: "argv: string[];",
    stated: { binders: [], params: [], result: readonlyArray(atom("string")) } },
  { host: contract, origin: node, global: "process", member: "execPath", signature: "execPath: string;",
    stated: { binders: [], params: [], result: atom("string") } },
  { host: contract, origin: node, global: "process", member: "pid", signature: "readonly pid: number;",
    stated: { binders: [], params: [], result: atom("number") } },
  // `process.execArgv`: the array of the Node options the process was
  // started with, built at start-up, read as `argv` is: a readonly view of
  // strings, an assumption that no code replaces it or writes a non-string.
  { host: contract, origin: node, global: "process", member: "execArgv", signature: "execArgv: string[];",
    stated: { binders: [], params: [], result: readonlyArray(atom("string")) } },
  // `process.platform` and `process.arch`: strings naming the operating
  // system and the processor Node was built for, fixed at start-up; the
  // declared unions of names are read as `string`.
  { host: contract, origin: node, global: "process", member: "platform", signature: "readonly platform: Platform;",
    stated: { binders: [], params: [], result: atom("string") } },
  { host: contract, origin: node, global: "process", member: "arch", signature: "readonly arch: Architecture;",
    stated: { binders: [], params: [], result: atom("string") } },
  // `process.env`: an object of the environment whose own entries hold
  // strings, its chain a prototype holding `constructor` and then
  // `Object.prototype`, which no accessor can be defined on: a readonly
  // dictionary of `string | undefined`, read at no key a prototype may
  // provide (the dictionary rule).
  { host: contract, origin: node, global: "process", member: "env", signature: "env: ProcessEnv;",
    stated: { binders: [], params: [], result: { k: "object", fields: [], calls: [], span: at,
      stringIndex: { readonly: true, value: optional(atom("string")), span: at } } } },
  // `process.exit(code)` runs the `exit` listeners synchronously, any of
  // which may throw into the caller, and otherwise ends the process: no
  // effect stated, the result `never`.
  ...["exit(code?: number | string | null): never;", "exit(code?: number | string | null | undefined): never;"].map(
    (signature): GlobalEntry => ({ host: contract, origin: node, global: "process", member: "exit", signature,
      stated: { binders: [], params: [optional(atom("number"))], result: atom("never") } })),
  // `process.kill(pid, signal)` sends the signal: `true`, a throw, or the
  // process ending; neither delivery nor termination is promised.
  { host: contract, origin: node, global: "process", member: "kill", signature: "kill(pid: number, signal?: string | number): true;",
    stated: { binders: [], params: [atom("number"), signal], result: { k: "literal", name: "true", text: "true", span: at } } },
  // Listener registration at a named event: `exit` and `beforeExit` call
  // the listener with the exit code, a signal with the signal's name, each
  // with the process as `this`, between synchronous jobs or within an
  // operation stating no effect (`process.exit`, `kill`). Registering emits
  // `newListener` and `once`'s removal `removeListener` synchronously, so the
  // call states no effect. The result is the process.
  ...["on", "once"].flatMap((method): GlobalEntry[] => [
    ...(["beforeExit", "exit"] as const).map((event): GlobalEntry => ({ host: contract, origin: node, global: "process", member: method,
      signature: `${method}(event: "${event}", listener: ${event === "exit" ? "ExitListener" : "BeforeExitListener"}): this;`,
      stated: { binders: [], params: [text(event), listener(atom("number"))], result: { k: "self", span: at } } })),
    // A signal name, or a string the call proves to be one: the listener
    // takes the name.
    ...[`${method}(event: Signals, listener: SignalsListener): this;`,
      `${method}(event: string | symbol, listener: (...args: any[]) => void): this;`].map((signature): GlobalEntry => (
      { host: contract, origin: node, global: "process", member: method, signature,
        stated: { binders: [], params: [signal, listener(atom("string"))], result: { k: "self", span: at } } }))]),
];

/** Node's `Buffer` and `TextDecoder` (SOURCE-CONTRACTS.md, "Stated library
 * types"), at the members the repository's code reads, each pinned to its
 * declaration in `@types/node`; the two texts of a member are the two pinned
 * installations' (the tools' and `library-project`'s). */
const bytesEntries: GlobalEntry[] = [
  // `Buffer.from(s)` with a string returns a fresh `Buffer` (Node 26.13.0's
  // `lib/buffer.js`, `fromString`), its own memory or a view into the
  // module's pool. It writes the string's UTF-8 bytes through the binding's
  // `utf8Write`, captured when the module loads, whose answer also sets the
  // view's length and the pool's next offset. It reads `Buffer.poolSize`, a
  // writable property of `Buffer` other code may make a getter, to choose:
  // no effect is stated.
  ...["from(string: WithImplicitCoercion<string>, encoding?: BufferEncoding): Buffer<ArrayBuffer>;",
    "from(data: WithImplicitCoercion<Uint8Array | readonly number[] | string>): Buffer<ArrayBuffer>;"].map(
    (signature): GlobalEntry => ({ host: contract, origin: node, global: "Buffer", member: "from", signature,
      stated: { binders: [], params: [atom("string")], result: buffer }, definitions: [stated.buffer] })),
  // `Buffer.compare(a, b)` checks that each is a `Uint8Array` by its
  // internal slots, throwing otherwise, and compares their bytes in the
  // native layer: `-1`, `0` or `1`. It runs no code and writes nothing on
  // normal return.
  { host: contract, origin: node, global: "Buffer", member: "compare",
    signature: "compare(buf1: Uint8Array, buf2: Uint8Array): -1 | 0 | 1;", effect: emptyEffect,
    stated: { binders: [], params: [bytes, bytes], result: { k: "union", span: at, parts: ["-1", "0", "1"].map(
      (n): TypeTerm => ({ k: "literal", name: "number", text: n, span: at })) } }, definitions: [stated.bytes] },
  // `new TextDecoder(label, options)` (Node 26.13.0's
  // `lib/internal/encoding.js`, the ICU build) converts the label by a
  // template, a string's own value, and throws where it names no supported
  // encoding; of the options it reads `fatal` and `ignoreBOM`, both stated,
  // by ToBoolean. It writes the decoder's state to symbol-keyed properties
  // of the fresh decoder, which a setter `TextDecoder.prototype` gets from
  // other code would intercept: no effect is stated.
  ...["TextDecoder: typeof globalThis extends {\n            onmessage: any;\n            TextDecoder: infer TextDecoder;\n        } ? TextDecoder\n            : typeof _TextDecoder"].map(
    (signature): GlobalEntry => ({ host: contract, origin: node, global: "TextDecoder", signature, constructs: true,
      stated: { binders: [], params: [optional(atom("string")), optional({ k: "object", stringIndex: null, calls: [], span: at,
        fields: ["fatal", "ignoreBOM"].map(name => ({ name, optional: true, readonly: true, type: optional(atom("boolean")), span: at })) })],
        result: textDecoder }, definitions: [stated.textDecoder, stated.bytes] })),
];

/** The standard library's `Uint8Array`, `Uint16Array`, `Int32Array` and
 * `Float64Array`
 * (SOURCE-CONTRACTS.md, "The standard library's typed arrays"), only
 * constructed, at a
 * length or an array of numbers: `new Uint8Array(n)` converts `n` by
 * ToIndex, a number's own value, throwing a `RangeError` where it is
 * negative or too large, and allocates a view of that many zeros, so at a
 * safe integer `n ≥ 0` a normal return's view has exactly `n` elements (the
 * first form's precondition and postcondition); `new
 * Uint8Array(xs)` of an array gets the array's `Symbol.iterator`, which an
 * array owns none of, from the untampered `Array.prototype`, steps the
 * standard array iterator, which reads `length` and each element, own data
 * properties or holes that no prototype holds, and converts each element,
 * a number or a hole's `undefined`, by ToNumber, which runs no code. Each
 * reads its prototype from the untampered constructor's `prototype` and
 * allocates: it runs no code of the client's and writes no location it did
 * not allocate. */
const lengthTerm = (kind: "value" | "view", slot: number): LinearTerm => ({ kind, slot, path: [] });
const viewOfLength: CallEffect = { ...emptyEffect,
  // At a call's positions: 1 the length, `int(1) ∧ 0 ≤ 1`.
  pre: [{ int: { slot: 1 } }, { linear: { fact: { le: { form: [[lengthTerm("value", 1), -1]], bound: 0 } } } }],
  // At a return's positions: 0 the view, 2 the length, `view(0) = 2`.
  ensures: [
    { linear: { fact: { le: { form: [[lengthTerm("view", 0), 1], [lengthTerm("value", 2), -1]], bound: 0 } } } },
    { linear: { fact: { le: { form: [[lengthTerm("view", 0), -1], [lengthTerm("value", 2), 1]], bound: 0 } } } }] };
const typedArrayEntries: GlobalEntry[] = viewKinds.map(({ name, type }): GlobalEntry => (
  { host: transparent("a length or an array of numbers, which no node list is"), global: name,
    signature: `${name}: ${name}Constructor`, constructs: true, effect: emptyEffect,
    forms: [{ binders: [], params: [atom("number")], result: type, effect: viewOfLength },
      { binders: [], params: [{ k: "union", span: at, parts: [atom("number"), readonlyArray(atom("number"))] }],
        result: type }], definitions: [...viewDefinitions] }));

/** The standard library's `Intl.Segmenter` (SOURCE-CONTRACTS.md,
 * "`Intl.Segmenter`"), only constructed, at its one construct signature: a
 * call of `%NewSegmenter%`, which states the constructor's steps at a locale
 * that is `undefined` or a string and options that are `undefined` or a
 * record of the two options it reads. */
const intlEntries: GlobalEntry[] = [
  ...["new (locales?: string | string[], options?: DateTimeFormatOptions): DateTimeFormat;",
    "new (locales?: LocalesArgument, options?: DateTimeFormatOptions): DateTimeFormat;"].map((signature): GlobalEntry => ({
      host: contract, global: "Intl", member: "DateTimeFormat", signature,
      intrinsic: newDateTimeFormatName, definitions: [stated.dateTimeFormat] })),
  { host: transparent("a locale and a record of string options, which no node list is"), global: "Intl",
    member: "Segmenter", signature: "new (locales?: LocalesArgument, options?: SegmenterOptions): Segmenter;",
    intrinsic: newSegmenterName, definitions: [stated.segmenter] },
];

/** Node's global `URL` (SOURCE-CONTRACTS.md, "Node's `URL`"), at the
 * declaration both pinned installations give it. */
const urlEntries: GlobalEntry[] = [
  // String input and string base go directly to the native parser.
  // A URL base could serialize externally aliased search parameters and
  // run client callbacks. The admitted strings avoid that path. The empty
  // footprint holds only on normal return. `new URL(…).href` reads the
  // fresh URL's serialization: Node's construction publishes the URL to no
  // other code, and `URL.prototype`'s `href` getter of a URL whose search
  // parameters no code has read serializes its parsed record, running no
  // other code under the untampered-standard-objects policy.
  { host: contract, origin: node, global: "URL", constructs: true, effect: emptyEffect,
    signature: "URL: typeof globalThis extends {\n            onmessage: any;\n            URL: infer T;\n        } ? T\n            : typeof _URL",
    serialized: urlHrefName, stated: { binders: [], params: [atom("string"), optional(atom("string"))],
      result: url }, definitions: [stated.url] },
];

/** The DOM's globals a client measures text with (SOURCE-CONTRACTS.md,
 * "The DOM's canvas, document and navigator"), each tested by `typeof`
 * before it is read, since a worker defines no `document` and Node no
 * `OffscreenCanvas`. `new OffscreenCanvas(width, height)` converts its
 * numbers by Web IDL's `[EnforceRange] unsigned long long`, which runs no
 * code on a number and throws a `TypeError` outside the range, and makes a
 * fresh canvas: it writes nothing it did not allocate. `document` and
 * `navigator` are `Window`'s attributes, the first `[LegacyUnforgeable]`,
 * each getter answering the one object the global holds, which no code
 * replaces under the untampered-standard-objects policy: constants of
 * their stated types. */
const domEntries: GlobalEntry[] = [
  { host: contract, global: "OffscreenCanvas", constructs: true, typeOf: typeOfOffscreenCanvasName, effect: emptyEffect,
    signature: "OffscreenCanvas: {\n    prototype: OffscreenCanvas;\n    new(width: number, height: number): OffscreenCanvas;\n}",
    stated: { binders: [], params: [atom("number"), atom("number")], result: canvas }, definitions: [stated.canvas] },
  { host: contract, global: "document", signature: "document: Document", constant: true, typeOf: typeOfDocumentName,
    stated: { binders: [], params: [], result: documentType }, definitions: [stated.document] },
  { host: contract, global: "navigator", signature: "navigator: Navigator", constant: true, typeOf: typeOfNavigatorName,
    stated: { binders: [], params: [], result: navigatorType }, definitions: [stated.navigator] },
  // CSSOM's `getComputedStyle(element)`, of one argument: the element's
  // resolved style, a declaration the host makes or reuses for it, whose
  // readonly flag is set. It updates the document's style, which runs no
  // code of the program's, and writes no location the model holds: the
  // empty footprint.
  { host: contract, global: "getComputedStyle",
    signature: "declare function getComputedStyle(elt: Element, pseudoElt?: string | null): CSSStyleDeclaration;",
    effect: emptyEffect, stated: { binders: [], params: [element], result: computedStyle },
    definitions: [stated.element, stated.computedStyle] },
];

/** The name the entries of `import.meta`'s members are keyed by. No
 * identifier spells it. */
export const importMetaName = "import.meta";
/** Node's `import.meta` (SOURCE-CONTRACTS.md, "Module metadata"), at the
 * members the repository's code reads, each pinned to its declaration in
 * `@types/node` (the tools' text, then `library-project`'s where it
 * differs) and read as a call of an intrinsic at `unknown` stating no
 * effect (`intrinsics.mts`). Node 26.13.0's
 * `DefaultImportMetaObjectInitializer` (`src/module_wrap.cc`) fills the
 * object at the module's first evaluation of `import.meta`, from the
 * module's wrapper, which other code reaches through `require.cache`: it
 * copies the wrapper's `url`, whatever value it holds, and reads its
 * `isMain`, where a getter other code defined runs
 * (`invalid-import-meta-url` and `invalid-import-meta-stale`, run under Node). For a `file:` URL
 * alone it defines `dirname` and `filename`, lazy data properties whose
 * first read converts the URL to a path in native code; and, outside the
 * loader hooks' worker thread, `resolve`, a lazy data property whose first
 * read makes the function by Node's own `createImportMetaResolve`. */
const importMetaEntries: GlobalEntry[] = [
  ...["url", "dirname", "filename"].map((member): GlobalEntry => ({ host: contract, origin: node,
    global: importMetaName, member, signature: `${member}: string;`, intrinsic: `%ImportMeta:${member}%` })),
  // `import.meta.resolve(specifier)` at one argument: the loader's
  // `resolveSync` converts the specifier by a template, a string's own
  // value, and runs every resolve hook `module.registerHooks` and
  // `module.register` installed, code of any module's. A URL a hook returns
  // is checked to be a string, but where a hook throws an error with the
  // code ERR_MODULE_NOT_FOUND or ERR_UNSUPPORTED_DIR_IMPORT and a truthy
  // `url`, that `url` is returned, whatever value it is
  // (`invalid-import-meta-resolve`, run under Node); without a truthy `url`
  // the error is thrown again. Node ignores a second argument unless
  // `--experimental-import-meta-resolve` is set. Absent on the loader hooks'
  // worker thread, where the call throws.
  ...["resolve(specifier: string, parent?: string | URL): string;",
    "resolve(specifier: string, parent?: string | URL | undefined): string;"].map((signature): GlobalEntry => (
    { host: contract, origin: node, global: importMetaName, member: "resolve", signature,
      intrinsic: "%ImportMeta:resolve%" })),
];

export const globalsOverlay: readonly GlobalEntry[] = [
  ...processEntries,
  ...bytesEntries,
  ...typedArrayEntries,
  ...intlEntries,
  ...urlEntries,
  ...domEntries,
  ...importMetaEntries,
  // Node's `console.log` and `console.error`, and the DOM's `console.error`,
  // as `console.log` below: each argument at a primitive, no effect stated.
  ...["log(message?: any, ...optionalParams: any[]): void;", "error(message?: any, ...optionalParams: any[]): void;",
    "error(...data: any[]): void;"].map((signature): GlobalEntry => ({
    ...(signature.includes("message") ? { origin: node } : {}),
    host: obligated("each argument", "the host formats every reachable key of an object argument"), global: "console",
    member: signature.startsWith("log") ? "log" : "error", signature,
    stated: signature.includes("message")
      ? { binders: [], params: [optional(primitive)], rest: primitive, result: atom("undefined") }
      : { binders: [], params: [], rest: primitive, result: atom("undefined") } })),
  // Output, which the model does not observe. Each argument is stated at a
  // primitive, which the host formats without calling a method of it, and
  // the call returns `undefined`. Writing the text calls the output
  // stream's `write`, a property other code may replace (`console.log`
  // keeping its identity), and a stream may call listeners other code
  // registered: no effect is stated, which covers that code.
  { host: obligated("each argument", "the host formats every reachable key of an object argument"), global: "console", member: "log", signature: "log(...data: any[]): void;",
    stated: { binders: [], params: [], rest: primitive, result: atom("undefined") } },
  // `BigInt(v)` throws a RangeError for a number that is not an integer and
  // a SyntaxError for a string that is not an integer's spelling; it runs no
  // code of the client's on a primitive, and returns a bigint otherwise. It
  // writes nothing: heap preservation.
  { host: contract, global: "BigInt", signature: "(value: bigint | boolean | number | string): bigint;", effect: emptyEffect },
  // A new symbol whose description is the argument converted to a string,
  // which a string or number never fails.
  { host: contract, global: "Symbol", signature: "(description?: string | number): symbol;" },
  // The registry's members, which read no receiver: each call is a call of
  // the intrinsic stating its step, so `Symbol` called and read through them
  // is a callable value of its call signature alone.
  { host: contract, global: "Symbol", member: "for", signature: "for(key: string): symbol;", intrinsic: symbolForName },
  { host: contract, global: "Symbol", member: "keyFor", signature: "keyFor(sym: symbol): string | undefined;",
    intrinsic: symbolKeyForName },
  // The well-known symbols, each a symbol: stated at `symbol`, since the
  // reader has no `unique symbol` type of a library property. Which symbol
  // each is, a key the library's types use, is not read.
  ...["iterator", "asyncIterator", "hasInstance", "toPrimitive", "toStringTag"].map(
    (member): GlobalEntry => ({ host: contract, global: "Symbol", member, signature: `readonly ${member}: unique symbol;`,
      stated: { binders: [], params: [], result: atom("symbol") } })),
  // `String(v)` called, with no new target (ECMA-262, "String ( value )"),
  // is `""` of no argument, SymbolDescriptiveString of a symbol, and
  // ToString of any other value: of a primitive without running client code;
  // of an object, ToPrimitive first, which calls its `Symbol.toPrimitive`,
  // or else its `toString` and `valueOf`, client code that may throw or
  // return an object, and then `String` throws. So the parameter is stated
  // at the primitives, where the call writes nothing and states heap
  // preservation. It reads its first argument alone and no receiver, so the
  // global may be read as a value (`xs.map(String)`): the callable taking a
  // primitive and any further arguments, which it ignores.
  { host: contract, global: "String", signature: "(value?: any): string;", value: true, effect: emptyEffect,
    stated: { binders: [], params: [primitive], rest: atom("unknown"), result: atom("string") } },
  // `Number(v)` converts a primitive without running client code: a bigint
  // to the nearest number, a symbol throws a TypeError, an outcome. An
  // object's conversion calls its `Symbol.toPrimitive`, `valueOf` or
  // `toString`, client code, so the parameter is stated at the primitives,
  // where the call writes nothing and states heap preservation. It reads its
  // first argument alone and no receiver, so the global may be read as a
  // value (`texts.map(Number)`): the callable taking a primitive and any
  // further arguments.
  { host: contract, global: "Number", signature: "(value?: any): number;", value: true, effect: emptyEffect,
    stated: { binders: [], params: [{ k: "union", span: at, parts: (["null", "undefined", "boolean", "number",
      "string", "bigint", "symbol"] as const).map(atom) }], rest: atom("unknown"), result: atom("number") } },
  // `Boolean(v)` is ToBoolean of its first argument, which reads no property
  // and runs no code of any value's, and ignores every further argument;
  // `Boolean()` is `false`; it reads no receiver. So the global may be read
  // as a value (`xs.filter(Boolean)`), the callable
  // `(value: unknown, ...rest: unknown[]) => boolean`. The declaration
  // promises no narrowing, and none is stated: its result is a Boolean, which
  // a guard's promise is not. It writes nothing: heap preservation.
  { host: contract, global: "Boolean", signature: "<T>(value?: T): boolean;", value: true, effect: emptyEffect,
    stated: { binders: [], params: [atom("unknown")], rest: atom("unknown"), result: atom("boolean") } },
  // `Math.max(...vs)` and `Math.min(...vs)` convert every argument with
  // ToNumber before comparing: a primitive without running code (`undefined`
  // and a string that spells no number to `NaN`; a symbol and a bigint throw
  // a TypeError, an outcome), an object by its own `Symbol.toPrimitive`,
  // `valueOf` or `toString`, code of the client's. So each argument is
  // stated at the primitives, a hole a spread reads (`undefined`) included.
  // The result is a number: `NaN` if any argument converts to `NaN`, and
  // `-Infinity` (`max`) or `Infinity` (`min`) of no argument. At primitives
  // they run no code and write nothing: the empty footprint, as the
  // `String` conversions below.
  ...["max", "min"].map((member): GlobalEntry => ({ host: contract, global: "Math", member, effect: emptyEffect,
    signature: `${member}(...values: number[]): number;`,
    stated: { binders: [], params: [], rest: primitive, result: atom("number") } })),
  // `String.fromCodePoint(...cs)` converts every argument with ToNumber, as
  // `Math.max` does, and throws a RangeError where the number is no integer
  // from 0 to 0x10FFFF, an outcome; otherwise its result is a string.
  { host: contract, global: "String", member: "fromCodePoint", signature: "fromCodePoint(...codePoints: number[]): string;", effect: emptyEffect,
    stated: { binders: [], params: [], rest: primitive, result: atom("string") } },
  // `String.fromCharCode(...cs)` likewise, each number taken modulo 2^16 to a
  // code unit, which never throws.
  { host: contract, global: "String", member: "fromCharCode", signature: "fromCharCode(...codes: number[]): string;", effect: emptyEffect,
    stated: { binders: [], params: [], rest: primitive, result: atom("string") } },
  // `String.raw` as a tag, `String.raw\`h${a}t\``: the tagged template
  // makes the frozen template object, whose own `raw` is the frozen array of
  // the raw strings, evaluates each substitution in order, then calls
  // `String.raw`, which reads `raw`'s `length` and each element, strings,
  // and converts each substitution by ToString between two of them. It runs
  // no code of the client's but the conversions, which the template of the
  // raw strings makes at its own `+` (`templateTag`). Read nowhere else.
  { host: contract, global: "String", member: "raw", templateTag: "raw", effect: emptyEffect,
    signature: "raw(template: { raw: readonly string[] | ArrayLike<string>; }, ...substitutions: any[]): string;" },
  // Tests of a number that convert nothing: `false` for any argument that is
  // not a number, an object included, whose methods are never read. They
  // write nothing.
  { host: contract, global: "Number", member: "isFinite", signature: "isFinite(number: unknown): boolean;", effect: emptyEffect },
  { host: contract, global: "Number", member: "isInteger", signature: "isInteger(number: unknown): boolean;", effect: emptyEffect },
  { host: contract, global: "Number", member: "isSafeInteger", signature: "isSafeInteger(number: unknown): boolean;",
    effect: emptyEffect },
  { host: contract, global: "Number", member: "isNaN", signature: "isNaN(number: unknown): boolean;", effect: emptyEffect },
  // `Number.POSITIVE_INFINITY`, a non-writable, non-configurable data
  // property of `Number` holding the number +∞: its read runs no code.
  { host: contract, global: "Number", member: "POSITIVE_INFINITY", signature: "readonly POSITIVE_INFINITY: number;" },
  // The global `Infinity`, a non-writable, non-configurable data property of
  // the global object holding the number +∞: its read runs no code, and no
  // code reassigns it. Read only as a value of its stated type.
  { host: contract, global: "Infinity", signature: "Infinity: number", constant: true,
    stated: { binders: [], params: [], result: atom("number") } },
  // The global `NaN`, a non-writable, non-configurable data property of the
  // global object holding the number NaN: read as `Infinity` is.
  { host: contract, global: "NaN", signature: "NaN: number", constant: true,
    stated: { binders: [], params: [], result: atom("number") } },
  // SameValue of the two arguments: identity of objects, equality of
  // primitives, no conversion and no client code, and no write. `any` is
  // read as `unknown`.
  { host: contract, global: "Object", member: "is", signature: "is(value1: any, value2: any): boolean;", effect: emptyEffect },
  // `Object.isFrozen(o)`: `true` of a primitive; of an object, its
  // [[IsExtensible]] and, where it is not extensible, its [[OwnPropertyKeys]]
  // and each key's [[GetOwnProperty]] (TestIntegrityLevel), which call no
  // getter and run no code on an ordinary object or one of ECMAScript's
  // exotic objects but a proxy (no object is one); a host object's may be
  // the host's own code, so the parameter is stated at the non-host values.
  // The result is a Boolean; no value of the object reaches the program,
  // and nothing is written.
  { host: obligated("the operand", "runs its [[IsExtensible]] and [[OwnPropertyKeys]], code of a host exotic object"),
    global: "Object", member: "isFrozen", signature: "isFrozen(o: any): boolean;", effect: emptyEffect,
    stated: { binders: [], params: [atom("nonHost")], result: atom("boolean") } },
  // `Object.freeze(o)` of an ordinary object makes every own property
  // non-writable and non-configurable and the object non-extensible, runs no
  // code (no object is a proxy) and returns `o`; a later write to it, or a
  // key added to it, throws, which no write of the model does. Admitted of a
  // fresh object literal of named fields alone, the overloads TypeScript
  // resolves such a call to, read as `%Freeze:K%`: its result, the only
  // reference to the object, holds the fields as readonly views, so no write
  // the program makes reaches it (SOURCE-FRAGMENT.md).
  ...["freeze<T extends { [idx: string]: U | null | undefined | object; }, U extends string | bigint | number | boolean | symbol>(o: T): Readonly<T>;",
    "freeze<T>(o: T): Readonly<T>;"].map((signature): GlobalEntry => ({ host: transparent("a fresh object literal, no host value"),
    global: "Object", member: "freeze", signature, freezes: true })),
  // `Object.hasOwn(o, k)`: ToObject of `o`, an object here, then the key, which
  // a string, number or symbol converts to without running code, then `o`'s
  // own lookup of it, [[GetOwnProperty]], which runs no code (no object is a
  // proxy, as for `Object.getOwnPropertyDescriptor`). The result is a
  // Boolean; no value of the object reaches the program, and nothing is
  // written.
  { host: contract, global: "Object", member: "hasOwn", signature: "hasOwn(o: object, v: PropertyKey): boolean;", effect: emptyEffect },
  // `Object.getPrototypeOf(o) === Object.prototype`: ToObject of `o` (a
  // TypeError of `null` or `undefined`), then its [[GetPrototypeOf]], which
  // runs no code on an ordinary object or one of ECMAScript's exotic objects
  // but a proxy (no object is one); a host object's may be the host's own
  // code, so the intrinsic takes a value that is no host object. Then
  // identity with the realm's `Object.prototype`, a non-writable,
  // non-configurable property of the untampered `Object`. Read only so: the
  // prototype itself, `Array.prototype` among the answers, an array outside
  // `Array`'s chain, never reaches the program
  // (`invalid-get-prototype-array-prototype`).
  { host: obligated("the operand", "runs its [[GetPrototypeOf]], code of a host exotic object"), global: "Object", member: "getPrototypeOf", signature: "getPrototypeOf(o: any): any;",
    prototypeTest: prototypeIsObjectName },
  // Reflect.apply invokes the target itself, never reading target.apply.
  // CreateListFromArrayLike reads length and indices, then Call supplies the
  // receiver. The existing receiver-application lowering checks the target,
  // receiver and array elements. Reflect requires a non-null argument list.
  { host: contract, global: "Reflect", member: "apply", receiverApply: true,
    signature: "function apply<T, A extends readonly any[], R>(\n        target: (this: T, ...args: A) => R,\n        thisArgument: T,\n        argumentsList: Readonly<A>,\n    ): R;" },
  { host: contract, global: "Reflect", member: "apply", receiverApply: true,
    signature: "function apply(target: Function, thisArgument: any, argumentsList: ArrayLike<any>): any;" },
  // `Reflect.ownKeys(o)` of a value that is no host object: its
  // [[OwnPropertyKeys]], which runs no code on an ordinary object or one of
  // ECMAScript's exotic objects but a proxy (no object is one; a host
  // object's may be the host's own code),
  // as a fresh dense array (CreateArrayFromList) of its own keys, strings
  // and symbols; no value of the object is read, and nothing else is
  // written. A primitive, which TypeScript's `object` excludes, is a
  // TypeError.
  { host: obligated("the operand", "runs its [[OwnPropertyKeys]], code of a host exotic object"), global: "Reflect", member: "ownKeys", signature: "function ownKeys(target: object): (string | symbol)[];",
    intrinsic: ownKeysName },
  // A fresh array of the object's own enumerable string keys: true of every
  // object, whatever its type says of its keys, and it runs no client code
  // (no getter is called) and writes only the array it allocates: the empty
  // footprint. ES5 declares it at `object`, ES2015 at `{}`.
  { host: transparent("a fresh array of strings, which is all its contract states"), global: "Object", member: "keys", signature: "keys(o: object): string[];", effect: emptyEffect },
  { host: transparent("a fresh array of strings, which is all its contract states"), global: "Object", member: "keys", signature: "keys(o: {}): string[];", effect: emptyEffect },
  // The values of those keys, and the key-value pairs: nothing is known of
  // them, `any` read as `unknown`, and each pair is a fresh array. Reading a
  // value runs an accessor's getter: the fragment writes none, and a host
  // object's is assumed to return.
  { host: obligated("the object", "hands the values of its own fields to the program"), global: "Object", member: "values", signature: "values(o: {}): any[];",
    stated: { binders: [], params: [atom("nonHost")], result: array(atom("unknown")) } },
  { host: obligated("the object", "hands the values of its own fields to the program"), global: "Object", member: "entries", signature: "entries(o: {}): [string, any][];",
    stated: { binders: [], params: [atom("nonHost")], result: array({ k: "tuple", presence: "dense", readonly: false,
      required: [atom("string"), atom("unknown")], optional: [], rest: null, span: at }) } },
  // `Object.getOwnPropertyDescriptor(o, k)`: ToObject of `o` (a TypeError of
  // `null` or `undefined`, an outcome; a primitive's wrapper otherwise), then
  // the key, which a string, number or symbol converts to without running
  // code, then `o`'s own lookup of it, [[GetOwnProperty]], which calls no
  // getter and runs no code on an ordinary or a built-in exotic object (a
  // proxy's would run its handler's trap: assumed of every object a program
  // holds, as `in` assumes it). The result is `undefined`, or a fresh
  // descriptor: `configurable` and `enumerable` Booleans, and `value` and
  // `writable`, or `get` and `set`. Nothing is known of `value`, a getter or
  // a setter: each is `unknown`, and the fields are stated readonly.
  { host: obligated("the object", "hands the values of its own fields to the program"), global: "Object", member: "getOwnPropertyDescriptor",
    signature: "getOwnPropertyDescriptor(o: any, p: PropertyKey): PropertyDescriptor | undefined;", ownString: ownStringName,
    stated: { binders: [], params: [atom("nonHost"),
      { k: "union", parts: [atom("string"), atom("number"), atom("symbol")], span: at }],
      result: optional(propertyDescriptor) } },
  // `Object.getOwnPropertyDescriptors(o)`: ToObject of `o` (a TypeError of
  // `null` or `undefined`, an outcome; a primitive's wrapper otherwise),
  // then its [[OwnPropertyKeys]] and, for each key, its [[GetOwnProperty]]:
  // neither calls a getter or runs code on an ordinary or a built-in exotic
  // object (no object is a proxy, as for the single form). Each descriptor
  // is a fresh object (FromPropertyDescriptor), defined on a fresh object at
  // its key (CreateDataPropertyOrThrow, a `"__proto__"` key included).
  // Stated as a dictionary of those descriptors at the string keys; nothing
  // is known of a `value`, a getter or a setter. Its fields are data
  // properties of objects no other reference holds, stated writable, as
  // the dictionary's index.
  { host: obligated("the object", "hands the values of its own fields to the program"), global: "Object", member: "getOwnPropertyDescriptors",
    signature: "getOwnPropertyDescriptors<T>(o: T): { [P in keyof T]: TypedPropertyDescriptor<T[P]>; } & { [x: string]: PropertyDescriptor; };",
    stated: { binders: [], params: [atom("nonHost")],
      result: { k: "object", fields: [], stringIndex: { readonly: false, value: freshDescriptor, span: at }, calls: [], span: at } } },
  // The generic overloads, which TypeScript selects for a record type whose
  // keys it does not bound, promise a `T` of every key's value. That is
  // true of a dictionary, whose every own string key holds a `T`
  // (`dictViewT`), and the parameter is stated at one: an open record may
  // own further keys of other types (`invalid-object-values-record.ts`),
  // and `ArrayLike<T>` is not read. Each pair is a fresh array. A
  // dictionary's keys hold data properties (the caller contract, and the
  // fragment's own objects), so each reads them without running code and
  // writes only what it allocates: the empty footprint.
  { host: transparent("the parameter is a dictionary, whose family admits no host object"), global: "Object", member: "values", signature: "values<T>(o: { [s: string]: T; } | ArrayLike<T>): T[];",
    effect: emptyEffect,
    stated: { binders: ["T"], params: [dictionary(binder("T"))], result: array(binder("T")) } },
  { host: transparent("the parameter is a dictionary, whose family admits no host object"), global: "Object", member: "entries", effect: emptyEffect,
    signature: "entries<T>(o: { [s: string]: T; } | ArrayLike<T>): [string, T][];",
    stated: { binders: ["T"], params: [dictionary(binder("T"))],
      result: array({ k: "tuple", presence: "dense", readonly: false, required: [atom("string"), binder("T")], optional: [],
        rest: null, span: at }) } },
  // A test of the array's identity, which the calculus makes itself
  // (`Tag.isArray`): true of exactly the objects that own an array store,
  // JavaScript's Array exotic objects. The declared guard, `arg is any[]`,
  // is not read: Lean narrows by the clauses of the tested value's type.
  { host: contract, global: "Array", member: "isArray", signature: "isArray(arg: any): arg is any[];", test: "isArray" },
  // `e instanceof Array`, entered by the variable's declaration: the same
  // test. `Array` owns no `[Symbol.hasInstance]`, and `Function.prototype`'s
  // cannot be replaced, so the operator walks `e`'s prototype chain for
  // `Array.prototype`. That finds it exactly for the arrays, under two
  // assumptions of the host: every array is made by the program's built-ins, and no
  // object inherits from `Array.prototype` but an array (the fragment makes
  // none: `class extends Array` and `Object.create` are refused, and it
  // cannot name `Array.prototype`).
  { host: contract, global: "Array", signature: "Array: ArrayConstructor", test: "isArray" },
  // `new Array()` and `new Array<T>()` are a fresh empty array, which is a
  // `T[]` at every `T`: the non-generic declaration's `any[]` states less
  // than that. An argument is refused: a single number is a length, and the
  // array it makes has holes, whose element contract would need a separate check.
  ...["new (arrayLength?: number): any[];", "new <T>(...items: T[]): T[];"].map(
    (signature): GlobalEntry => ({ host: contract, global: "Array", signature,
      stated: { binders: ["T"], params: [], result: { k: "array", presence: "readable", readonly: false, element: binder("T"), span: at } } })),
  // `new Array<T>(n)` makes `n` holes, which a readable `T[]` admits only
  // where `undefined` meets `T`: read only where `fill(v)`, the standard
  // library's, of one argument, is called directly on it. ArrayCreate checks
  // the length (a RangeError where ToUint32(n) ≠ n), `fill` is
  // `Array.prototype`'s, it reads the fresh array's own `length`, takes 0
  // and the length for the omitted bounds without converting anything, and
  // sets each index to `v`: neither prototype owns a numeric key, so each
  // set defines a data property of the array, which no code holds until
  // `fill` returns it. So the expression is `%ArrayFilled%(%ArrayLength%(n),
  // v)`, in JavaScript's order: `n`, the check, `v`, then the array, whose
  // allocation no code observes.
  { host: contract, global: "Array", signature: "new <T>(arrayLength: number): T[];",
    filled: { length: arrayLengthName, fill: arrayFilledName } },
  // `new Error(m)` with a string owns `message`, that string, as a property
  // that is not enumerable, and inherits `name` from `Error.prototype`: the
  // model holds both on a prototype it gives the object, so a read and `in`
  // find them and a spread does not copy them (`errorInstance`). A missing
  // message is `Error.prototype`'s, so the message is required. `stack` is
  // the engine's and is not stated.
  //
  // ES2022's `options`: after converting the message, the host runs
  // InstallErrorCause (ECMA-262, "Error ( message [ , options ] )"): where
  // `options` is an object and `HasProperty(options, "cause")` holds, it
  // reads `Get(options, "cause")` and defines the value as the error's own
  // non-enumerable data property `cause`. The options are stated at
  // `errorOptions`, at which neither step runs code. The error's own
  // `cause`, like `stack`, is not stated: a read of it is refused, and a
  // write of it is reserved (`errorOwnedKeys` in Lean's lowering).
  //
  // `Error(m)` called runs the same steps: with no new target, the error
  // constructor takes itself as the target (ECMA-262, "Error ( message [ ,
  // options ] )"), so the call is read as the construct, at the same
  // statement. It converts a string message with no code of the client's
  // and writes nothing it did not allocate: the empty footprint, on a throw
  // too. Its normal result is an ordinary object whose own locations are
  // freshly allocated (`nonHostObject` and `freshObject`).
  ...["new (message?: string): Error;", "new (message?: string, options?: ErrorOptions): Error;",
    "(message?: string): Error;", "(message?: string, options?: ErrorOptions): Error;"].map(
    (signature): GlobalEntry => ({ host: contract, global: "Error", signature,
      ...(signature.startsWith("new ") ? {} : { construct: true }), effect: footprintEffect(emptyFootprint, { onThrow: true, freshObject: true }),
      stated: { binders: [], params: signature.includes("options") ? [atom("string"), errorOptions(at)] : [atom("string")],
        result: { k: "intersection", span: at, parts: [errorInstance(at), atom("nonHostObject")] } } })),
  // `new TypeError(m)` with a string is ECMA-262's NativeError constructor
  // ("NativeError ( message [ , options ] )") at a string message without
  // options, or with options read as `Error`'s: the steps of `Error`'s,
  // with `TypeError.prototype`, whose `name` is `"TypeError"` and which
  // inherits from `Error.prototype`, as the error's prototype. The error
  // owns `message` and inherits `name`, as `errorInstance` states; it
  // converts a string message with no code of the client's and writes
  // nothing it did not allocate: the empty footprint, on a throw too.
  // `new RangeError(m)` likewise, with `RangeError.prototype`, whose `name`
  // is `"RangeError"` and which inherits from `Error.prototype`.
  ...(["TypeError", "RangeError"] as const).flatMap(global =>
    [`new (message?: string): ${global};`, `new (message?: string, options?: ErrorOptions): ${global};`].map(
    (signature): GlobalEntry => ({ host: contract, global, signature, effect: footprintEffect(emptyFootprint, { onThrow: true }),
      stated: { binders: [], params: signature.includes("options") ? [atom("string"), errorOptions(at)] : [atom("string")],
        result: errorInstance(at) } }))),
  // `parseInt(s, radix)` converts `s` by ToString and `radix` by ToInt32,
  // which run no code on a string and a number, the calculus's primitive
  // types its declaration states: a number, `NaN` where `s` spells none.
  // It writes nothing: the empty footprint.
  { host: contract, global: "parseInt", signature: "declare function parseInt(string: string, radix?: number): number;",
    effect: emptyEffect },
  // The DOM's global `atob(data)`, of the HTML standard's
  // WindowOrWorkerGlobalScope (Node's global `atob` follows the same
  // algorithm): Web IDL converts `data` to a DOMString, which runs no code
  // on a string, then the forgiving-base64 decode makes a fresh string of
  // the decoded bytes, one code unit each, or throws an
  // `InvalidCharacterError` DOMException, an outcome. It writes nothing:
  // the empty footprint, on a throw too.
  { host: contract, global: "atob", signature: "declare function atob(data: string): string;",
    effect: footprintEffect(emptyFootprint, { onThrow: true }) },
  // `parseFloat(s)` converts `s` by ToString, which runs no code on a string,
  // the primitive its declaration states: a number, `NaN` where no prefix of
  // `s` spells one. It writes nothing: the empty footprint.
  { host: contract, global: "parseFloat", signature: "declare function parseFloat(string: string): number;",
    effect: emptyEffect },
  // Node's global `clearTimeout(t)`, declared in `@types/node`: of a
  // number or a string, it cancels the timer of that id; of an object, it
  // reads and clears the object's `_onTimeout` and unlinks the timer, which
  // for an object that is no timer reads and writes its properties, which
  // may be accessors; of anything else it does nothing. It returns
  // `undefined`. Stated at any value, and with no effect. The two texts are
  // the two pinned `@types/node` installations' (the tools' and
  // `library-project`'s).
  ...["function clearTimeout(timeout: NodeJS.Timeout | string | number | undefined): void;",
    "function clearTimeout(timeoutId: NodeJS.Timeout | string | number | undefined): void;"].map(
    (signature): GlobalEntry => ({ host: contract, origin: node, global: "clearTimeout", signature,
      stated: { binders: [], params: [atom("unknown")], result: atom("undefined") } })),
  // Node's global `setTimeout(callback, delay)` schedules the callback, which
  // the host calls with no argument after the delay, between synchronous
  // jobs, as a listener is called (SOURCE-CONTRACTS.md, "Node's process"),
  // and returns the timer, an object read at no member. Scheduling runs
  // asynchronous-resource hooks other code may have installed: no effect is
  // stated. The callback states no effect either.
  ...["function setTimeout<TArgs extends any[]>(\n            callback: (...args: TArgs) => void,\n            delay?: number,\n            ...args: TArgs\n        ): NodeJS.Timeout;",
    "function setTimeout(callback: (_: void) => void, delay?: number): NodeJS.Timeout;",
    "function setTimeout<TArgs extends any[]>(\n            callback: (...args: TArgs) => void,\n            ms?: number,\n            ...args: TArgs\n        ): NodeJS.Timeout;",
    "function setTimeout(callback: (args: void) => void, ms?: number): NodeJS.Timeout;"].map(
    (signature): GlobalEntry => ({ host: contract, origin: node, global: "setTimeout", signature,
      stated: { binders: [], params: [{ k: "function", effect: ordinaryEffect, receiver: null, params: [], rest: null,
        result: atom("unknown"), span: at }, optional(atom("number"))], result: atom("unknown") } })),
  // Node's global `structuredClone(value)` serializes its argument, reading
  // every own enumerable property by [[Get]], so a getter runs, and builds a
  // fresh copy of data properties, its prototypes `Object.prototype`, its
  // symbol keys dropped; a function throws a `DataCloneError`. A getter may
  // change what the traversal reads later, so the copy of a `JsonValue` may
  // be none (Node 25.2.1, and Node 26.13.0 on 2026-11-05: a getter beside an
  // array's elements popping an enclosing array leaves a hole in its copy). Stated at any value, the
  // result `unknown`, no effect stated; a transfer list is not admitted.
  ...["function structuredClone<T>(\n            value: T,\n            options?: { transfer?: Transferable[] },\n        ): T;",
    "function structuredClone<T>(\n        value: T,\n        transfer?: { transfer: ReadonlyArray<import(\"worker_threads\").TransferListItem> },\n    ): T;"].map(
    (signature): GlobalEntry => ({ host: contract,
      origin: node, global: "structuredClone", signature,
      stated: { binders: [], params: [atom("unknown")], result: atom("unknown") } })),
  // `Math.abs(x)`, `Math.ceil(x)`, `Math.floor(x)`, `Math.round(x)`,
  // `Math.fround(x)` and `Math.sign(x)` of a number, a primitive: no
  // conversion code runs.
  { host: contract, global: "Math", member: "abs", signature: "abs(x: number): number;", effect: emptyEffect },
  { host: contract, global: "Math", member: "ceil", signature: "ceil(x: number): number;", effect: emptyEffect },
  { host: contract, global: "Math", member: "floor", signature: "floor(x: number): number;", effect: emptyEffect },
  { host: contract, global: "Math", member: "sign", signature: "sign(x: number): number;", effect: emptyEffect },
  { host: contract, global: "Math", member: "round", signature: "round(x: number): number;", effect: emptyEffect },
  { host: contract, global: "Math", member: "fround", signature: "fround(x: number): number;", effect: emptyEffect },
  // `Math.random()`: a number in [0, 1); it reads no argument and writes no
  // location a program can reach.
  { host: contract, global: "Math", member: "random", signature: "random(): number;", effect: emptyEffect },
  // `Object.fromEntries(entries)` iterates `entries` and, for each element,
  // reads its 0 and 1, converts the key by ToPropertyKey and defines it as
  // an own data property of a fresh object (CreateDataPropertyOrThrow, a
  // `"__proto__"` key included). Over an array, its iterator is the host's
  // (`%Iterate%`), and a pair `readonly [string, T]` is an array whose
  // positions hold data: no code runs, and nothing it did not allocate is
  // written. A program's iterable would run its iterator, client code, and
  // a key of another type its conversion: stated at an array of string-keyed
  // pairs, its result a dictionary of `T`.
  { host: transparent("an array of pairs, which no node list is"), global: "Object", member: "fromEntries",
    signature: "fromEntries<T = any>(entries: Iterable<readonly [PropertyKey, T]>): { [k: string]: T; };", effect: emptyEffect,
    stated: { binders: ["T"], params: [readonlyArray({ k: "tuple", presence: "dense", readonly: true,
      required: [atom("string"), binder("T")], optional: [], rest: null, span: at })],
      result: { k: "object", fields: [], stringIndex: { readonly: false, value: binder("T"), span: at }, calls: [], span: at } } },
  // `Array.from(xs)` of an array copies it through its iterator, the
  // host's, reading the current length at each step: a fresh dense array of
  // its elements, a hole read as `undefined`, which a readable `T[]` holds
  // only where `undefined` meets `T`. It writes nothing else.
  //
  // `Array.from(s)` of a string steps the string's iterator,
  // `String.prototype[Symbol.iterator]`, whose `next` yields each code point
  // of `s` as a string of one or two code units (a lone surrogate as itself),
  // and defines each on a fresh array: a dense `string[]`. The string is a
  // primitive, so no step runs client code; it writes nothing else. Both
  // forms are stated at either declaration, since the host takes the same
  // steps whichever TypeScript resolves.
  ...["from<T>(arrayLike: ArrayLike<T>): T[];", "from<T>(iterable: Iterable<T> | ArrayLike<T>): T[];"].map(
    (signature): GlobalEntry => ({ host: transparent("the array's store: a node list's table"), global: "Array",
      member: "from", signature, effect: emptyEffect,
      forms: [{ binders: ["T"], params: [readonlyArray(binder("T"))], result: array(binder("T")) },
        { binders: ["T"], params: [atom("string")], result: array(atom("string")) }] })),
  // `Array.from(items, f)` reads `items[Symbol.iterator]`: where `items`
  // has one, it steps that iterator, and otherwise reads `items.length`
  // (ToLength, no code on a number) and each index; it calls `f` with each
  // value and its index, and defines `f`'s results on a fresh array. A
  // record `{ readonly length: number }` may hold an iterator or accessors
  // of its own, client code yielding any value: `f` takes `unknown`, and the
  // call states no effect, as `f` and that code may change anything. The
  // result is a fresh dense array of `f`'s results.
  //
  // `Array.from(s, f)` of a string steps the string's iterator, as without
  // `f`, and calls `f` with each code point, a string, and its index: `f`
  // takes a string. `f` may change anything but the string, a primitive,
  // so the traversal yields every code point; the result, a fresh array `f`
  // never receives, is dense. The call states no effect, as `f` states none.
  ...["from<T, U>(arrayLike: ArrayLike<T>, mapfn: (v: T, k: number) => U, thisArg?: any): U[];",
    "from<T, U>(iterable: Iterable<T> | ArrayLike<T>, mapfn: (v: T, k: number) => U, thisArg?: any): U[];"].map(
    (signature): GlobalEntry => ({ host: transparent("the record's length or its iterator, whose values the callback takes at unknown"),
      global: "Array", member: "from", signature,
      forms: [{ binders: ["U"], params: [
        { k: "object", stringIndex: null, calls: [], span: at,
          fields: [{ name: "length", optional: false, readonly: true, type: atom("number"), span: at }] },
        { k: "function", effect: ordinaryEffect, receiver: null, params: [atom("unknown"), atom("number")], rest: null,
          result: binder("U"), span: at }],
        result: array(binder("U")) },
      { binders: ["U"], params: [atom("string"),
        { k: "function", effect: ordinaryEffect, receiver: null, params: [atom("string"), atom("number")], rest: null,
          result: binder("U"), span: at }],
        result: array(binder("U")) }] })),
  // `new RegExp(pattern, flags)` of strings compiles the pattern, a
  // SyntaxError where the pattern or the flags are invalid, an outcome. A
  // regex `pattern` would be read by its `Symbol.match`, `source` and
  // `flags`, which an object may hold as accessors: stated at strings. The
  // pattern is known only at run time, so its capture shape and flags are
  // not: the result is the structural regex a `RegExp` annotation states
  // (SOURCE-CONTRACTS.md, "Regular expressions"), whose members state no
  // effect, the native mark not stated. It writes nothing it did not
  // allocate, on its throw too.
  ...["new (pattern: RegExp | string, flags?: string): RegExp;", "new (pattern: string, flags?: string): RegExp;",
    "new (pattern: RegExp | string): RegExp;"].map((signature): GlobalEntry => ({ host: contract, global: "RegExp", signature,
      effect: footprintEffect(emptyFootprint, { onThrow: true }),
      stated: library => ({ binders: [], params: signature.includes("flags")
        ? [atom("string"), optional(atom("string"))] : [atom("string")], result: library("RegExp", []) }) })),
  // `e instanceof Error`: `Error` owns no `[Symbol.hasInstance]` and
  // `Function.prototype`'s cannot be replaced, so the operator walks `e`'s
  // prototype chain for `Error.prototype`, a data property that is neither
  // writable nor configurable: no code runs, no object being a proxy, and
  // nothing is written. The answer says nothing of `e`'s fields: an object
  // gets `Error.prototype` without `Error` constructing it
  // (`Object.create`, a class extending `Error`), so the test narrows
  // nothing (SOURCE-FRAGMENT.md), and is read as the intrinsic stating the
  // Boolean alone.
  { host: contract, global: "Error", signature: "Error: ErrorConstructor", intrinsic: instanceOfErrorName },
  // `e instanceof Map` and `e instanceof Set`: neither owns a
  // `[Symbol.hasInstance]`, so the operator walks `e`'s prototype chain for
  // `Map.prototype` or `Set.prototype`, as for `Error`. The answer `true`
  // promises `e` the collection's reading view, by the host assumption that
  // a value passing the test is a host collection (`intrinsics.mts`).
  { host: contract, global: "Map", signature: "Map: MapConstructor", intrinsic: instanceOfMapName },
  { host: contract, global: "Set", signature: "Set: SetConstructor", intrinsic: instanceOfSetName },
  // PromiseResolve retains a native promise with the built-in standard
  // constructor, and freshly resolves stably non-thenable values. Without a
  // value, the promise settles to `undefined`, as an async completion does.
  { host: contract, global: "Promise", member: "resolve", signature: "resolve<T>(value: T): Promise<Awaited<T>>;",
    intrinsic: promiseResolveName },
  { host: contract, global: "Promise", member: "resolve", signature: "resolve(): Promise<void>;", intrinsic: asyncCompleteName },
  // `%PromiseAll%`: an array of promises, each settling to its type
  // argument as `%Await%` assumes, gives a promise of the array of their
  // values. The declaration's parameter, values of any kind each adopted, is
  // stated as an array of promises.
  { host: transparent("elements at Promise types: realm promises by the await assumption"), global: "Promise", member: "all",
    signature: "all<T extends readonly unknown[] | []>(values: T): Promise<{ -readonly [P in keyof T]: Awaited<T[P]>; }>;",
    intrinsic: promiseAllName },
  // `new Set<T>(xs)` is a fresh set of the array's elements, `new Set<T>()`
  // an empty one, at every `T`. An array's iterator is the host's, which
  // runs no client code; any other iterable's is the client's, so the
  // parameter is stated at an array (`Set<T>`: `array-prototype.mts`). The
  // construction reads the array and allocates, so it states the empty
  // footprint; so does `new Map`'s. The iterable overload is stated at an
  // array and, separately, at a string, whose iterator is the host's too:
  // `new Set(s)` is a fresh set of the string's code points, a
  // `Set<string>`. One form at `readonly T[] | string` would be false at
  // `T := number`.
  //
  // The iterable overload is stated, third, at a host `Set`'s reading view
  // (`NativeSetView<T>`, which a `Set<T>` meets): `new Set(s)` gets
  // `s[Symbol.iterator]`, the host's `Set` iterator by the assumption
  // `%Iterate:Set%` makes of a value at the view, steps it with the host's
  // `next`, which runs no client code, and adds each element by
  // `Set.prototype.add`, which it gets from the fresh set, whose prototype
  // is the untampered `Set.prototype`. It reads `s` and allocates.
  // A further form admits an array or the host view at one element type,
  // including a host set with an empty-array fallback.
  { host: transparent("the array's store: a node list's table"), global: "Set", signature: "new <T = any>(values?: readonly T[] | null): Set<T>;", effect: emptyEffect,
    stated: library => ({ binders: ["T"], params: [optional(readonlyArray(binder("T")))],
      result: library("Set", [binder("T")]) }) },
  { host: transparent("the array's store: a node list's table"), global: "Set", signature: "new <T>(iterable?: Iterable<T> | null): Set<T>;", effect: emptyEffect,
    forms: (library, view) => [
      { binders: ["T"], params: [optional(readonlyArray(binder("T")))], result: library("Set", [binder("T")]) },
      { binders: ["T"], params: [atom("string")], result: library("Set", [atom("string")]) },
      { binders: ["T"], params: [view("Set", [binder("T")])], result: library("Set", [binder("T")]) },
      { binders: ["T"], params: [{ k: "union", parts: [readonlyArray(binder("T")), view("Set", [binder("T")])], span: at }], result: library("Set", [binder("T")]) }] },
  // Only empty construction: no iterator, entry access or overridden adder runs.
  ...["new <K extends WeakKey = WeakKey, V = any>(entries?: readonly (readonly [K, V])[] | null): WeakMap<K, V>;",
    "new <K extends WeakKey = WeakKey, V = any>(iterable?: Iterable<readonly [K, V]> | null): WeakMap<K, V>;"]
    .map((signature): GlobalEntry => ({ host: transparent("empty native collection allocation"), global: "WeakMap", signature,
      effect: emptyEffect, stated: library => ({ binders: ["K", "V"], params: [],
        result: library("WeakMap", [binder("K"), binder("V")]) }) })),
  // `new Map<K, V>(es)` is a fresh map of the array's pairs, each read at
  // its indices 0 and 1, and `new Map()` an empty one, at every `K` and `V`.
  //
  // The iterable overload is stated, second, at a host `Map`'s reading view
  // (`NativeMapView<K, V>`, which a `Map<K, V>` meets): `new Map(m)` steps
  // the host's `Map` iterator, by the assumption `%Iterate:Map%` makes of a
  // value at the view, which yields a fresh `[key, value]` array per entry;
  // it reads each entry's `0` and `1`, own data elements of that fresh
  // array, so no getter runs, and sets them by `Map.prototype.set`, which
  // it gets from the fresh map, whose prototype is the untampered
  // `Map.prototype`. It reads `m` and allocates. An undefined argument
  // returns the empty map before looking up `set` or obtaining an iterator.
  ...["new (): Map<any, any>;", "new <K, V>(entries?: readonly (readonly [K, V])[] | null): Map<K, V>;",
    "new <K, V>(iterable?: Iterable<readonly [K, V]> | null): Map<K, V>;"]
    .map((signature): GlobalEntry => ({ host: transparent("an array of pairs, which no node list is"), global: "Map", signature, effect: emptyEffect,
      forms: (library, view) => {
        const pairs: Stated = { binders: ["K", "V"],
          params: [optional(readonlyArray({ k: "tuple", presence: "dense", readonly: true, required: [binder("K"), binder("V")],
            optional: [], rest: null, span: at }))],
          result: library("Map", [binder("K"), binder("V")]) };
        return signature.includes("Iterable") ? [pairs, { binders: ["K", "V"], params: [view("Map", [binder("K"), binder("V")])],
          result: library("Map", [binder("K"), binder("V")]) }, { binders: ["K", "V"], params: [optional(view("Map", [binder("K"), binder("V")]))],
          result: library("Map", [binder("K"), binder("V")]) }] : [pairs];
      } })),
  // `new Date()` is now; `new Date(v)` converts a number or a string without
  // client code, but a `Date` argument, which any object meeting the
  // interface is, is converted by its own `valueOf` or `toString`: it is
  // stated at the primitives. With several numbers, each is a component.
  // An invalid date is a `Date` all the same, whose getters give `NaN`.
  { host: contract, global: "Date", signature: "new (): Date;" },
  ...["new (value: number | string): Date;", "new (value: number | string | Date): Date;"]
    .map((signature): GlobalEntry => ({ host: contract, global: "Date", signature,
      stated: library => ({ binders: [], params: [{ k: "union", parts: [atom("number"), atom("string")], span: at }],
        result: library("Date", []) }) })),
  { host: contract, global: "Date",
    signature: "new (year: number, monthIndex: number, date?: number, hours?: number, minutes?: number, seconds?: number, ms?: number): Date;" },
  // The current time, a number.
  { host: contract, global: "Date", member: "now", signature: "now(): number;" },
  // `JSON.parse(text)` is a fresh `ParsedJson` built from the text, or a
  // SyntaxError. It runs no code of the client's and writes only what it
  // allocates, also before it throws: the empty footprint, on a throw too.
  // A reviver is client code the host would call on every member, and whose
  // results replace them: the call is read with the text only.
  { host: contract, global: "JSON", member: "parse",
    signature: "parse(text: string, reviver?: (this: any, key: string, value: any) => any): any;",
    stated: { binders: [], params: [atom("string")], result: parsedJson }, definitions: [parsedJsonDefinition],
    effect: footprintEffect(emptyFootprint, { onThrow: true }) },
  // `JSON.stringify(v)` returns `undefined` for `undefined`, a symbol or a
  // function, calls a `toJSON` it finds, and throws on a bigint or a cycle;
  // at a `JsonValue` it does none of the first two and returns a string. A
  // replacer is client code: the call is read with the value, a replacer
  // that is `null` or absent, and an indent that is a primitive number or
  // string, which `ToIntegerOrInfinity` or the string's own characters give
  // without running code. At a `JsonValue` it runs no code of the client's
  // and writes nothing: it reads own data properties and allocates the
  // string, also before it throws on a cycle, so the empty footprint holds
  // on a throw too.
  { host: transparent("the parameter is JsonValue, whose serialization enumerates the keys of no host object (HOST-FAMILIES.md, Excluding host values)"), global: "JSON", member: "stringify",
    signature: "stringify(value: any, replacer?: (this: any, key: string, value: any) => any, space?: string | number): string;",
    stated: { binders: [], params: [jsonValue, optional(atom("null")),
      optional({ k: "union", parts: [atom("number"), atom("string")], span: at })], result: atom("string") },
    definitions: [jsonValueDefinition],
    effect: footprintEffect(emptyFootprint, { onThrow: true }) },
  // The overload whose replacer is a list of keys, which `JSON.stringify`
  // reads by its length and indices, primitive numbers and strings whose
  // conversion runs no code; or `null` or absent, as the other.
  { host: transparent("the parameter is JsonValue, whose serialization enumerates the keys of no host object (HOST-FAMILIES.md, Excluding host values)"), global: "JSON", member: "stringify",
    signature: "stringify(value: any, replacer?: (number | string)[] | null, space?: string | number): string;",
    stated: { binders: [], params: [jsonValue, optional({ k: "union", span: at, parts: [atom("null"),
      readonlyArray({ k: "union", parts: [atom("number"), atom("string")], span: at })] }),
      optional({ k: "union", parts: [atom("number"), atom("string")], span: at })], result: atom("string") },
    definitions: [jsonValueDefinition],
    effect: footprintEffect(emptyFootprint, { onThrow: true }) },
  // `%PromiseReject%`: a promise rejected with the reason, whose await
  // throws it, an outcome; it settles to no value, so it is a promise of
  // every type. The declared `any` is read as `unknown`: nothing runs on it.
  { host: contract, global: "Promise", member: "reject", signature: "reject<T = never>(reason?: any): Promise<T>;",
    intrinsic: promiseRejectName },
  // `%NewPromise%`: the executor is called at once with the promise's
  // resolving functions, and a throw out of it rejects the promise. The
  // declared `resolve` adopts a thenable (`T | PromiseLike<T>`); stated, it
  // takes a primitive, on which it settles.
  { host: contract, global: "Promise",
    signature: "new <T>(executor: (resolve: (value: T | PromiseLike<T>) => void, reject: (reason?: any) => void) => void): Promise<T>;",
    intrinsic: newPromiseName },
];

/** A declaration-text matcher preserves array stores on normal return. */
export type GlobalSignatureMatcher = (signature: string) =>
  Within<{ value: "any"; store: "keep" }, boolean>;

/** Search entries by global, member (absent: its call), signature and origin. */
export function globalEntry(entries: readonly GlobalEntry[], global: string, member: string | undefined,
    matches: GlobalSignatureMatcher, origin: string): Within<{ value: "any"; store: "keep" }, GlobalEntry | undefined> {
  return entries.find(e => e.global === global && e.member === member && matches(e.signature) &&
    (e.origin ?? "library") === origin);
}

/** The origins a global's entries admit: a declaration of it from any other
 * is no declaration the overlay reviews. */
export function globalOrigins(entries: readonly GlobalEntry[], global: string): Set<string> {
  return new Set(entries.filter(e => e.global === global).map(e => e.origin ?? "library"));
}
