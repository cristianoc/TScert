/** Node's and the standard library's types a client may name whose values
 * the reader states instead of reading their declarations: a reviewed overlay
 * of type names (SOURCE-CONTRACTS.md, "Stated library types"), as
 * `library-modules.mts` states Node's module functions. An entry names the
 * type's declaration parts, each by where it comes from and its heading
 * exactly as reviewed, so a changed or added part is refused and reviewed
 * again, and states the type the host's values of that name meet, at the
 * members the overlay states: a definition of its own, which every reference
 * to the name denotes and which the module and global entries returning such
 * values name. The declarations are not read, so the types they name
 * (`ArrayBufferLike`, `ImplicitArrayBuffer`) are not collected. */
import type { DeclarationIdentity, TypeDefinition, TypeTerm } from "./declaration-types.mts";
import { emptyEffect, ordinaryEffect } from "./type-graph.mts";
import type { CallEffect } from "./type-graph.mts";

export type TypeEntry = {
  /** The type's name, as a client writes it: `Buffer`. */
  name: string;
  /** Every declaration part TypeScript binds the name to as a type, merged
   * ones included: where it comes from, as `declarationOrigin` names it
   * (`library`, `@types/node`), and its heading, the text before its body,
   * white space collapsed, exactly as reviewed. A value the name also
   * declares (`var Buffer`) is the name's other meaning, read as a global. */
  parts: { origin: string; heading: string }[];
  /** The type the host's values of the name meet. */
  definition: TypeDefinition;
  /** The type arguments TypeScript must give the name, where its
   * declaration takes any, when it types a value from its context, for a
   * statement that holds at these alone (a `Dirent`'s names are strings at
   * `Dirent<string>`); absent, it holds at every argument. */
  arguments?: TypeTerm[];
};

type AtomName = Extract<TypeTerm, { k: "atom" }>["name"];
type Field = Extract<TypeTerm, { k: "object" }>["fields"][number];
const at: [number, number] = [0, 0];
const atom = (name: AtomName): TypeTerm => ({ k: "atom", name, span: at });
const text = (value: string): TypeTerm => ({ k: "literal", name: "string", text: value, span: at });
const union = (...parts: TypeTerm[]): TypeTerm => ({ k: "union", parts, span: at });
const field = (name: string, type: TypeTerm, readonly: boolean = true): Field => ({ name, optional: false, readonly, type, span: at });
/** A method of the value's prototype: its receiver the value. */
const method = (params: TypeTerm[], result: TypeTerm, effect: CallEffect = ordinaryEffect): TypeTerm =>
  ({ k: "function", effect, receiver: { k: "self", span: at }, params, rest: null, result, span: at });
const identity = (name: string): DeclarationIdentity => ({ module: "tscert/node", name, span: at });
const named = (id: DeclarationIdentity): TypeTerm =>
  ({ k: "reference", args: [], span: at, reference: { name: id.name, span: at, arguments: [], target: id } });
const definitionOf = (id: DeclarationIdentity, expression: TypeTerm): TypeDefinition =>
  ({ declaration: id, parameters: [], bases: [], expression });

/** A view of bytes: a `Uint8Array`, or a `Buffer`, read at what the host
 * gives it (ECMA-262, "TypedArray Objects"),
 *
 *     type Uint8Array = { readonly [k: number]: number; readonly length: number };
 *
 * A canonical numeric key that is a valid index holds its byte, a number
 * from 0 to 255, as a data property; any other reads `undefined`, the host
 * never looking along the prototype chain at a numeric key. `length` is
 * `%TypedArray%.prototype`'s getter, which reads the view's own slots and
 * runs no other code. The model holds it as the view's own readonly member,
 * where JavaScript holds it on the prototype chain: only an observation of
 * own keys tells them apart, and none is typed at what it would tell
 * (SOURCE-CONTRACTS.md, "Stated library types"). The index is readonly: a
 * write converts its value by ToNumber, which runs an object's `valueOf`,
 * and is not stated. */
const bytesIdentity = identity("Uint8Array");
export const bytes: TypeTerm = named(bytesIdentity);
const length = field("length", atom("number"));
const elements = { readonly: true, value: atom("number"), span: at };
const bytesDefinition = definitionOf(bytesIdentity,
  { k: "object", fields: [length], stringIndex: null, numberIndex: elements, calls: [], span: at });

/** A `Buffer`, a view of bytes with the methods of `Buffer.prototype` the
 * overlay states (Node 25.2.1's `lib/buffer.js`),
 *
 *     type Buffer = { readonly [k: number]: number; readonly length: number;
 *       toString(encoding: "utf8"): string; subarray(start: number, end?: number): Buffer };
 *
 * `toString("utf8")` reads `this.length` and calls `this.utf8Slice`, and
 * `subarray(start, end)` reads `this.length`, `this.buffer` and
 * `this.byteOffset`, clamps its integers and constructs a `FastBuffer` over
 * the same memory: a fresh `Buffer`. Under the host assumption that these
 * members are the host's own (SOURCE-CONTRACTS.md, "Stated library types"),
 * neither runs code of the client's nor writes a location it did not
 * allocate. */
const bufferIdentity = identity("Buffer");
export const buffer: TypeTerm = named(bufferIdentity);
export const bufferDefinition: TypeDefinition = definitionOf(bufferIdentity,
  { k: "object", stringIndex: null, numberIndex: elements, calls: [], span: at, fields: [length,
    field("toString", method([text("utf8")], atom("string"), emptyEffect)),
    field("subarray", method([atom("number"), union(atom("number"), atom("undefined"))], buffer, emptyEffect))] });

/** The tests a `Stats`, a `BigIntStats` and a `Dirent` dispatch through a
 * prototype other code may change: each `() => unknown`, its effect
 * unrestricted. */
const tests: Field[] = ["isFile", "isDirectory", "isBlockDevice", "isCharacterDevice", "isSymbolicLink", "isFIFO",
  "isSocket"].map(name => field(name, method([], atom("unknown"))));

/** What `statSync(path, { bigint: true })` returns (Node 25.2.1's
 * `lib/internal/fs/utils.js`): `StatsBase` and `BigIntStats` assign the
 * eighteen bigints, which become own writable data properties under the
 * host assumption that a `BigIntStats` keeps its audited prototype chain, as
 * a `Stats` does (SOURCE-CONTRACTS.md, "Library modules"),
 *
 *     type BigIntStats = { dev, mode, …, birthtimeNs: bigint; isFile(): unknown; … };
 */
const bigIntStatsIdentity = identity("BigIntStats");
export const bigIntStats: TypeTerm = named(bigIntStatsIdentity);
const bigIntStatsDefinition = definitionOf(bigIntStatsIdentity, { k: "object", stringIndex: null, calls: [], span: at,
  fields: [...["dev", "mode", "nlink", "uid", "gid", "rdev", "blksize", "ino", "size", "blocks", "atimeMs", "mtimeMs",
    "ctimeMs", "birthtimeMs", "atimeNs", "mtimeNs", "ctimeNs", "birthtimeNs"].map(name => field(name, atom("bigint"), false)),
  ...tests] });

/** An entry `readdirSync(path, { withFileTypes: true })` lists: a `Dirent`,
 * or a `DirentFromStats`, owning `name` and `parentPath`, writable strings
 * (SOURCE-CONTRACTS.md, "Library modules"),
 *
 *     type Dirent = { name: string; parentPath: string; isFile(): unknown; … };
 */
const direntIdentity = identity("Dirent");
export const dirent: TypeTerm = named(direntIdentity);
const direntDefinition = definitionOf(direntIdentity, { k: "object", stringIndex: null, calls: [], span: at,
  fields: [field("name", atom("string"), false), field("parentPath", atom("string"), false), ...tests] });

/** What `new TextDecoder(label, options)` constructs (Node 25.2.1's
 * `lib/internal/encoding.js`),
 *
 *     type TextDecoder = { decode(input: Uint8Array): string };
 *
 * `decode` is `TextDecoder.prototype`'s method. It reads the decoder's state
 * through symbol-keyed properties, on which other code may install a getter,
 * and, outside UTF-8 and windows-1252, the decoder's `encoding` getter,
 * which other code may replace: it states no effect. A view of bytes it
 * decodes to a string; a malformed one, at `fatal: true`, throws. */
const textDecoderIdentity = identity("TextDecoder");
export const textDecoder: TypeTerm = named(textDecoderIdentity);
export const textDecoderDefinition: TypeDefinition = definitionOf(textDecoderIdentity,
  { k: "object", stringIndex: null, calls: [], span: at, fields: [field("decode", method([bytes], atom("string")))] });

export const definitions: { bytes: TypeDefinition; buffer: TypeDefinition; bigIntStats: TypeDefinition;
  dirent: TypeDefinition; textDecoder: TypeDefinition } = { bytes: bytesDefinition, buffer: bufferDefinition,
  bigIntStats: bigIntStatsDefinition, dirent: direntDefinition, textDecoder: textDecoderDefinition };

const node = "@types/node";
const library = "library";
export const typesOverlay: readonly TypeEntry[] = [
  // The standard library's `Uint8Array`, as the configured standard library
  // declares it in parts, and Node's part adding `at`.
  { name: "Uint8Array", definition: bytesDefinition, parts: [
    { origin: library, heading: "interface Uint8Array<TArrayBuffer extends ArrayBufferLike = ArrayBufferLike> {" },
    { origin: library, heading: "interface Uint8Array<TArrayBuffer extends ArrayBufferLike> {" },
    { origin: node, heading: "interface Uint8Array extends RelativeIndexable<number> {" }] },
  { name: "Buffer", definition: bufferDefinition, parts: [
    { origin: node, heading: "interface Buffer<TArrayBuffer extends ArrayBufferLike = ArrayBufferLike> extends Uint8Array<TArrayBuffer> {" },
    { origin: node, heading: "interface Buffer {" }] },
  { name: "BigIntStats", definition: bigIntStatsDefinition, parts: [
    { origin: node, heading: "export interface BigIntStats extends StatsBase<bigint> {" }] },
  { name: "Dirent", definition: direntDefinition, arguments: [atom("string")], parts: [
    { origin: node, heading: "export class Dirent<Name extends string | Buffer = string> {" },
    { origin: node, heading: "export class Dirent {" }] },
];

/** The entry stating `name`, where every part TypeScript binds it to as a
 * type is one of the entry's, exactly as reviewed; null where no entry names
 * it or none of the parts is one it reviews (another type of that name, a
 * program's). A name with a part the entry reviews and one it does not, a
 * changed declaration or one merged into it, is refused. */
export function typeEntry(name: string, parts: readonly { origin: string; heading: string }[]): TypeEntry | null {
  const entry = typesOverlay.find(e => e.name === name);
  const reviewed = (p: { origin: string; heading: string }): boolean =>
    !!entry?.parts.some(r => r.origin === p.origin && r.heading === p.heading);
  if (!entry || !parts.some(reviewed)) return null;
  const unreviewed = parts.find(p => !reviewed(p));
  if (unreviewed)
    throw Error(`${name} is stated by the overlay of library types, which does not review its declaration ${unreviewed.heading} (${unreviewed.origin})`);
  return entry;
}
