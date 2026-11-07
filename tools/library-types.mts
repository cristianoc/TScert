/** Node's and the standard library's types a client may name whose values
 * the reader states instead of reading their declarations: a reviewed overlay
 * of type names (SOURCE-CONTRACTS.md, "Stated library types"), as
 * `library-modules.mts` states Node's module functions. An entry names the
 * type's declaration parts, each by where it comes from and its heading
 * exactly as reviewed, so a changed or added part is refused and reviewed
 * again, and states the type the host's values of that name meet, at the
 * members the overlay states: a definition of its own, which every reference
 * to the name denotes and which the module and global entries returning such
 * values name. The pin is of the headings alone: the statement is audited
 * against the host's code, which the declarations' bodies do not describe.
 * The declarations are not read, so the types they name (`ArrayBufferLike`,
 * `ImplicitArrayBuffer`) are not collected. */
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
  /** A view of bytes: an element read at a number and a read of `length` of
   * a value TypeScript types at the name are `%ByteAt%` and `%ByteLength%`. */
  view?: "bytes";
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

/** The marker of a view of bytes: a host object (HOST-FAMILIES.md, "Host
 * objects"), which the model holds as owning `[[host]]` at this string and
 * no allocation of the program owns, so no program object meets a view's
 * type. */
export const bytesMarker = "node:bytes";

/** A view of bytes: a `Uint8Array`, a `Uint16Array`, an `Int32Array`, a
 * `Float64Array`, or a `Buffer`, a host object read at what the host gives
 * it (ECMA-262, "TypedArray Objects"), each a typed array whose elements
 * are numbers (a `Float64Array`'s any double, `NaN` included),
 *
 *     type Uint8Array = host "node:bytes" {
 *       readonly [[viewLength]]: number;   // stable
 *       fill(value: number, start?: number, end?: number): Uint8Array;
 *       copyWithin(target: number, start: number, end?: number): Uint8Array;
 *       set(source: Uint8Array, offset?: number): undefined;
 *       subarray(begin: number, end?: number): Uint8Array };
 *
 * The four standard names denote this one type: every member it states
 * holds of each of them alike. Its elements and its `length` are read
 * through `%ByteAt%` and `%ByteLength%`, and an element written through
 * `%ByteSet%` (`intrinsics.mts`), which the parser writes for an element
 * read or write at a number and a read of `length` of a value TypeScript
 * types as a view: the host's [[Get]] and [[Set]] of an integer-indexed
 * exotic object at a canonical numeric key, which never read the prototype
 * chain, and `%TypedArray%.prototype`'s `length` getter. The model holds no
 * element and no `length` of it: a host object refuses the operations
 * copying its own properties or exposing their values, `Object.keys` and
 * `Object.hasOwn` answer strings and Booleans no type tells, and no record
 * type naming `length` admits a view.
 *
 * The methods are `%TypedArray%.prototype`'s (ECMA-262, "Properties of the
 * %TypedArray% Prototype Object"), each called at numbers and views alone:
 * ToNumber and ToIntegerOrInfinity of a number run no code, `set` of a view
 * copies by SetTypedArrayFromTypedArray, which runs none, and `subarray`'s
 * TypedArraySpeciesCreate reads the view's `constructor` and its
 * `Symbol.species`, the standard constructor and `%TypedArray%`'s getter
 * under the host assumption below, and constructs a fresh view over the
 * same memory. `fill` and `copyWithin` return the receiver. Each writes the
 * view's elements alone, which the model holds no location of, and throws
 * a `RangeError` where an index is out of range: within the empty
 * footprint. `map`, `filter`, `slice` and the other members, a species
 * constructor's or a callback's, are not stated. */
const bytesIdentity = identity("Uint8Array");
export const bytes: TypeTerm = named(bytesIdentity);
const optionalNumber = union(atom("number"), atom("undefined"));
/** The members of `%TypedArray%.prototype` a view states, each returning
 * `self` where it returns the receiver or a view of its kind. */
const viewMethods = (self: TypeTerm): Field[] => [
  field("fill", method([atom("number"), optionalNumber, optionalNumber], self, emptyEffect)),
  field("copyWithin", method([atom("number"), atom("number"), optionalNumber], self, emptyEffect)),
  field("set", method([bytes, optionalNumber], atom("undefined"), emptyEffect)),
  field("subarray", method([atom("number"), optionalNumber], self, emptyEffect))];
/** The element count a view's model key `[[viewLength]]` holds, a
 * readonly `number` the host owns at a location no other object's field or
 * store shares, one value for the view's life (DESIGN.md, "Trust surface"):
 * a stable key (HOST-FAMILIES.md, "Stable keys"), so every step keeps a
 * fact naming the count (PROGRAM-TYPING.md, "Linear facts"). */
const viewLength: Field = field("[[viewLength]]", atom("number"));
const bytesDefinition = definitionOf(bytesIdentity,
  { k: "object", fields: [viewLength, ...viewMethods(bytes)], stringIndex: null, calls: [], host: bytesMarker,
    stable: ["[[viewLength]]"], span: at });

/** A `Buffer`, a view of bytes with the methods of `Buffer.prototype` the
 * overlay states (Node 26.13.0's `lib/buffer.js`),
 *
 *     type Buffer = host "node:bytes" { toString(encoding: "utf8"): string;
 *       fill(value: number, offset?: number, end?: number): Buffer;
 *       copyWithin(target: number, start: number, end?: number): Buffer;
 *       set(source: Uint8Array, offset?: number): undefined;
 *       subarray(start: number, end?: number): Buffer };
 *
 * `toString("utf8")` reads the view's length from its internal slot and
 * decodes through the binding's `utf8Slice`, and `subarray(start, end)`
 * reads the length from the slot, `this.buffer` and `this.byteOffset`, clamps its integers and constructs a `FastBuffer` over
 * the same memory: a fresh `Buffer`. `fill` of a number validates its
 * offsets as integers within the view, throwing otherwise, reads
 * `this.length` and the byte length, and calls the realm's
 * `%TypedArray%.prototype.fill` captured at startup; it returns the
 * receiver. `copyWithin` and `set` are `%TypedArray%.prototype`'s, as for
 * any view. Under the host assumption that these members are the host's
 * own (SOURCE-CONTRACTS.md, "Stated library types"), none runs code of the
 * client's nor writes a location the model holds. A `Buffer` is a
 * `Uint8Array`: it has the marker and more. */
const bufferIdentity = identity("Buffer");
export const buffer: TypeTerm = named(bufferIdentity);
export const bufferDefinition: TypeDefinition = definitionOf(bufferIdentity,
  { k: "object", stringIndex: null, calls: [], host: bytesMarker, stable: ["[[viewLength]]"], span: at, fields: [
    viewLength, field("toString", method([text("utf8")], atom("string"), emptyEffect)), ...viewMethods(buffer)] });

/** The tests a `Stats`, a `BigIntStats` and a `Dirent` dispatch through a
 * prototype other code may change: each `() => unknown`, its effect
 * unrestricted. */
const tests: Field[] = ["isFile", "isDirectory", "isBlockDevice", "isCharacterDevice", "isSymbolicLink", "isFIFO",
  "isSocket"].map(name => field(name, method([], atom("unknown"))));

/** What `statSync(path, { bigint: true })` returns (Node 26.13.0's
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

/** What `new TextDecoder(label, options)` constructs (Node 26.13.0's
 * `lib/internal/encoding.js`),
 *
 *     type TextDecoder = { decode(input: Uint8Array): string };
 *
 * `decode` is `TextDecoder.prototype`'s method, under the host assumption
 * that it is Node's own data property throughout execution and that no
 * decoder owns a `decode` (SOURCE-CONTRACTS.md, "Node's `Buffer` and
 * `TextDecoder`"). It reads the decoder's state
 * through symbol-keyed properties, on which other code may install a getter:
 * it states no effect. A view of bytes it
 * decodes to a string; a malformed one, at `fatal: true`, throws. */
const textDecoderIdentity = identity("TextDecoder");
export const textDecoder: TypeTerm = named(textDecoderIdentity);
export const textDecoderDefinition: TypeDefinition = definitionOf(textDecoderIdentity,
  { k: "object", stringIndex: null, calls: [], span: at, fields: [field("decode", method([bytes], atom("string")))] });

/** The marker of a WHATWG URL: a host object (HOST-FAMILIES.md, "Host
 * objects"), as a view of bytes is. */
export const urlMarker = "node:url";

/** An opaque host URL. Property reads can invoke own getters or serialize
 * externally aliased search parameters; this view admits no member access. */
const urlIdentity = identity("URL");
export const url: TypeTerm = named(urlIdentity);
const urlDefinition: TypeDefinition = definitionOf(urlIdentity,
  { k: "object", stringIndex: null, calls: [], host: urlMarker, span: at,
    fields: [] });

/** A segment `Intl.Segments`' iterator yields (ECMA-402,
 * CreateSegmentDataObject): a fresh ordinary object, `Object.prototype` its
 * prototype, owning `segment`, `index` and `input` as data properties, and
 * `isWordLike` where the segmenter's granularity is `"word"`,
 *
 *     type SegmentData = { segment: string; index: number; input: string; isWordLike?: boolean };
 */
const segmentDataIdentity = identity("SegmentData");
export const segmentData: TypeTerm = named(segmentDataIdentity);
const segmentDataDefinition = definitionOf(segmentDataIdentity, { k: "object", stringIndex: null, calls: [], span: at,
  fields: [field("segment", atom("string"), false), field("index", atom("number"), false), field("input", atom("string"), false),
    { name: "isWordLike", optional: true, readonly: false, type: atom("boolean"), span: at }] });

/** The marker of an `Intl.Segments`: a host object (HOST-FAMILIES.md, "Host
 * objects"), as a view of bytes is. */
export const segmentsMarker = "intl:segments";

/** What `Intl.Segmenter.prototype.segment` returns (ECMA-402,
 * CreateSegmentsObject): a fresh object of `%IntlSegmentsPrototype%`
 * holding the segmenter and the string in internal slots,
 *
 *     type Segments = host "intl:segments" {};
 *
 * A `for...of` over one steps `%Iterate:Segments%` (`intrinsics.mts`),
 * yielding `SegmentData`. It states no member: `containing` is not read. */
const segmentsIdentity = identity("Segments");
export const segments: TypeTerm = named(segmentsIdentity);
export const segmentsDefinition: TypeDefinition = definitionOf(segmentsIdentity,
  { k: "object", stringIndex: null, calls: [], host: segmentsMarker, span: at, fields: [] });

/** The marker of an `Intl.Segmenter`: a host object (HOST-FAMILIES.md,
 * "Host objects"), as a view of bytes is. */
export const segmenterMarker = "intl:segmenter";

/** What `new Intl.Segmenter(locales, options)` constructs (ECMA-402,
 * "Segmenter Objects"),
 *
 *     type Segmenter = host "intl:segmenter" { segment(input: string): Segments };
 *
 * `segment` is `%IntlSegmenterPrototype%`'s method: it checks the
 * receiver's `[[SegmenterLocale]]` slot, throwing a `TypeError` where it
 * has none, converts a string by ToString, its own value, and allocates a
 * `Segments` over the segmenter and the string, running no code and writing
 * no location it did not allocate. `resolvedOptions` is not stated. */
const segmenterIdentity = identity("Segmenter");
export const segmenter: TypeTerm = named(segmenterIdentity);
export const segmenterDefinition: TypeDefinition = definitionOf(segmenterIdentity,
  { k: "object", stringIndex: null, calls: [], host: segmenterMarker, span: at,
    fields: [field("segment", method([atom("string")], segments, emptyEffect))] });

/** The DOM's host objects a client measures text with (SOURCE-CONTRACTS.md,
 * "The DOM's canvas, document and navigator"), each a platform object of
 * the HTML standard whose stated members are attributes, getters on its
 * interface's prototype, and operations, data properties there: the
 * members a client reads or calls, at the types the standard gives them,
 * and no other. Each is a host object (HOST-FAMILIES.md, "Host objects"):
 * no allocation of the program meets its type, and the steps that copy or
 * expose an object's own properties refuse it. */
const domIdentity = (name: string): DeclarationIdentity => ({ module: "tscert/dom", name, span: at });

/** The marker of a `TextMetrics`. */
export const textMetricsMarker = "dom:text-metrics";
/** What `measureText` returns (HTML, "Drawing text to the bitmap"): a fresh
 * `TextMetrics`, whose attributes are numbers the call computed,
 *
 *     type TextMetrics = host "dom:text-metrics" {
 *       readonly width: number;
 *       readonly actualBoundingBoxLeft: number;
 *       readonly actualBoundingBoxRight: number };
 *
 * each getter returning the value it holds, which nothing changes. */
const textMetricsIdentity = domIdentity("TextMetrics");
export const textMetrics: TypeTerm = named(textMetricsIdentity);
const textMetricsDefinition = definitionOf(textMetricsIdentity, { k: "object", stringIndex: null, calls: [],
  host: textMetricsMarker, span: at, fields: ["width", "actualBoundingBoxLeft", "actualBoundingBoxRight"]
    .map(name => field(name, atom("number"))) });

/** The marker of a 2D context, a `CanvasRenderingContext2D` or an
 * `OffscreenCanvasRenderingContext2D`. */
export const canvasContextMarker = "dom:canvas-2d";
/** A 2D context, of a canvas element or of an `OffscreenCanvas` (HTML,
 * "The 2D rendering context"): the two interfaces share
 * `CanvasTextDrawingStyles` and `CanvasText`, the member stated,
 *
 *     type CanvasRenderingContext2D = host "dom:canvas-2d" { measureText(text: string): TextMetrics };
 *
 * `measureText(text)` converts `text` by Web IDL's DOMString, which runs no
 * code on a string, shapes it under the context's current state and returns
 * a fresh `TextMetrics`: it writes no location the model holds, within the
 * empty footprint. The context's text drawing state is the host's, which
 * the model holds no location of: a read of an attribute the context
 * states a getter for (`canvasGetters`) and a write of one it states a
 * setter for (`canvasSetters`) are calls of their intrinsics, as an
 * element of a view of bytes is read and written. Any other member, read or
 * written, is refused. */
const canvasContextIdentity = domIdentity("CanvasRenderingContext2D");
export const canvasContext: TypeTerm = named(canvasContextIdentity);
const canvasContextDefinition = definitionOf(canvasContextIdentity, { k: "object", stringIndex: null, calls: [],
  host: canvasContextMarker, span: at, fields: [field("measureText", method([atom("string")], textMetrics, emptyEffect))] });

/** A context's getters a client reads (HTML, `CanvasTextDrawingStyles`),
 * each `o.k` of a value TypeScript types as 2D contexts only, written by the
 * parser as a call of its intrinsic `%CanvasGet:k%(o)` (`intrinsics.mts`):
 * `font` serializes the context's current font, a string, and
 * `letterSpacing` its letter spacing, a string, or `undefined` in a host
 * that predates the attribute (Safari before 18), where no object of the
 * context's chain holds the key. Each runs no code and writes nothing. */
export const canvasGetters: readonly { member: string; type: TypeTerm; intrinsic: string }[] = [
  { member: "font", type: atom("string") },
  { member: "letterSpacing", type: union(atom("string"), atom("undefined")) },
].map(g => ({ ...g, intrinsic: `%CanvasGet:${g.member}%` }));

/** A context's setters a client writes (HTML, `CanvasTextDrawingStyles`),
 * each `o.k = v` of a value TypeScript types as 2D contexts only, an
 * intersection with one among them (as `"lang" in o` narrows it), written
 * by the parser as a call of its intrinsic `%CanvasSet:k%(o, v)`, at the
 * type of the values it takes (`intrinsics.mts`): Web IDL converts `v` to a
 * DOMString, which runs no code on a string, and the setter parses it and
 * sets the context's state, ignoring a value it does not parse (a font, a
 * letter spacing) or one no enumeration value names; in a host that
 * predates the attribute, the assignment creates an own data property of
 * the context at `v`, which no stated member reads. It changes the
 * context's state alone, which the model holds no location of, and runs no
 * other code. */
export const canvasSetters: readonly { member: string; value: TypeTerm; intrinsic: string }[] = [
  { member: "font", value: atom("string") },
  { member: "letterSpacing", value: atom("string") },
  { member: "lang", value: atom("string") },
  { member: "fontKerning", value: union(text("auto"), text("normal"), text("none")) },
  { member: "textRendering", value: union(text("auto"), text("optimizeSpeed"), text("optimizeLegibility"),
    text("geometricPrecision")) },
].map(s => ({ ...s, intrinsic: `%CanvasSet:${s.member}%` }));

/** A canvas a 2D context is made from, an `OffscreenCanvas` or a canvas
 * element (HTML, "The canvas element", "The OffscreenCanvas interface"),
 *
 *     type Canvas = host "dom:canvas" { getContext(id: "2d"): CanvasRenderingContext2D | null };
 *
 * `getContext("2d")` makes the canvas's 2D context the first time, returns
 * it at every later call, and returns `null` where the canvas has a context
 * of another kind: it runs no code and writes only the canvas's own slots,
 * which the model holds no location of, within the empty footprint. A
 * canvas element made in a document that is not an HTML document is an
 * `Element` in no namespace, which has no `getContext`: the call throws a
 * `TypeError`, an outcome. */
export const canvasMarker = "dom:canvas";
const canvasIdentity = domIdentity("OffscreenCanvas");
export const canvas: TypeTerm = named(canvasIdentity);
const canvasDefinition = definitionOf(canvasIdentity, { k: "object", stringIndex: null, calls: [],
  host: canvasMarker, span: at, fields: [
    field("getContext", method([text("2d")], union(canvasContext, atom("null")), emptyEffect))] });

/** An element (DOM, "Interface Element"), at the member a client reads of
 * any element, its root among them,
 *
 *     type Element = host "dom:element" { readonly lang: string | undefined };
 *
 * `lang` is `HTMLElement`'s attribute, the getter reflecting the content
 * attribute, a string; an element of another namespace (an SVG document's
 * root) has none on its chain and reads `undefined`. Tree mutation and
 * rectangle measurement retain unrestricted effects. HTML elements
 * additionally expose their inline style. */
export const elementMarker = "dom:element";
const elementIdentity = domIdentity("Element");
export const element: TypeTerm = named(elementIdentity);
const rectangleIdentity = domIdentity("DOMRect");
const rectangle: TypeTerm = named(rectangleIdentity);
const rectangleDefinition = definitionOf(rectangleIdentity, { k: "object", stringIndex: null, calls: [],
  host: "dom:rectangle", span: at, fields: [field("width", atom("number"))] });
const elementDefinition = definitionOf(elementIdentity, { k: "object", stringIndex: null, calls: [],
  host: elementMarker, span: at, fields: [field("lang", union(atom("string"), atom("undefined"))),
    field("appendChild", method([element], element)), field("removeChild", method([element], element)),
    field("getBoundingClientRect", method([], rectangle))] });

/** Browser inline declarations and rectangles. Mutating calls retain unrestricted
 * effects, including custom-element reactions and exceptional exits. */
const inlineStyleIdentity = domIdentity("InlineStyle");
export const inlineStyle: TypeTerm = named(inlineStyleIdentity);
const inlineStyleDefinition = definitionOf(inlineStyleIdentity, { k: "object", stringIndex: null, calls: [],
  host: "dom:inline-style", span: at, fields: [
    field("setProperty", method([atom("string"), atom("string"), union(atom("string"), atom("undefined"))], atom("undefined")))] });
const htmlElementIdentity = domIdentity("HTMLElement");
export const htmlElement: TypeTerm = named(htmlElementIdentity);
const htmlElementDefinition = definitionOf(htmlElementIdentity, { k: "intersection", span: at, parts: [element,
  { k: "object", stringIndex: null, calls: [], span: at, fields: [field("style", inlineStyle)] }] });

// createElement has no HTML namespace in a non-HTML document. Such an element
// has no inline style; the client checks this optional member before writing it.
const spanElementIdentity = domIdentity("CreatedSpan");
const spanElement: TypeTerm = named(spanElementIdentity);
const spanElementDefinition = definitionOf(spanElementIdentity, { k: "intersection", span: at, parts: [element,
  { k: "object", stringIndex: null, calls: [], span: at,
    fields: [field("style", union(inlineStyle, atom("undefined")))] }] });

/** Accessor assignments execute a host operation and return the assigned value.
 * CSSStyleDeclaration annotations remain the readonly computed-style view;
 * the cssText operation additionally requires the inline-style host marker. */
export const domSetters: readonly { member: string; value: TypeTerm; receiver: TypeTerm; intrinsic: string }[] = [
  { member: "cssText", value: atom("string"), receiver: inlineStyle, intrinsic: "%DOMSet:cssText%" },
  { member: "textContent", value: union(atom("string"), atom("null")), receiver: element, intrinsic: "%DOMSet:textContent%" },
];

const dateTimeFormatIdentity = { module: "tscert/intl", name: "DateTimeFormat", span: at };
export const dateTimeFormat: TypeTerm = named(dateTimeFormatIdentity);
const dateTimeFormatDefinition = definitionOf(dateTimeFormatIdentity, { k: "object", stringIndex: null, calls: [],
  host: "intl:date-time-format", span: at, fields: [field("resolvedOptions", method([], {
    k: "object", stringIndex: null, calls: [], span: at, fields: [field("locale", atom("string"))] }))] });

/** What `getComputedStyle(element)` returns (CSSOM, "Extensions to the
 * Window interface"): the element's resolved style, a `CSSStyleDeclaration`
 * whose readonly flag is set, at the member a client reads,
 *
 *     type ComputedStyle = host "dom:computed-style" { readonly width: string };
 *
 * `width` is `CSSStyleProperties`'s getter, the resolved value of the
 * property serialized, a string: a length in `px` where the element has a
 * box, its computed value, `auto`, where it has none. */
export const computedStyleMarker = "dom:computed-style";
const computedStyleIdentity = domIdentity("CSSStyleDeclaration");
export const computedStyle: TypeTerm = named(computedStyleIdentity);
const computedStyleDefinition = definitionOf(computedStyleIdentity, { k: "object", stringIndex: null, calls: [],
  host: computedStyleMarker, span: at, fields: [field("width", atom("string"))] });

/** The global `document` (HTML, `Window`'s `[LegacyUnforgeable] readonly
 * attribute Document document`), at the members a client reads,
 *
 *     type Document = host "dom:document" {
 *       readonly documentElement: Element | null;
 *       readonly body: HTMLElement | null; readonly head: HTMLElement | null;
 *       createElement(localName: "canvas"): Canvas;
 *       createElement(localName: "span"): CreatedSpan };
 *
 * `documentElement` is the getter answering the document's root element,
 * `null` in a document with none. `createElement("canvas")` makes a fresh
 * canvas element: the name is no valid custom element name, so no
 * constructor of the program's runs, and it writes nothing the model holds,
 * within the empty footprint. */
export const documentMarker = "dom:document";
const documentIdentity = domIdentity("Document");
export const documentType: TypeTerm = named(documentIdentity);
const documentDefinition = definitionOf(documentIdentity, { k: "object", stringIndex: null, calls: [],
  host: documentMarker, span: at, fields: [field("documentElement", union(element, atom("null"))),
    field("body", union(htmlElement, atom("null"))), field("head", union(htmlElement, atom("null"))),
    field("createElement", { k: "intersection", span: at, parts: [method([text("canvas")], canvas, emptyEffect),
      method([text("span")], spanElement)] })] });

/** The global `navigator` (HTML, `Window`'s `readonly attribute Navigator
 * navigator`, and `WorkerGlobalScope`'s), at the members a client reads,
 *
 *     type Navigator = host "dom:navigator" { readonly userAgent: string; readonly platform: string };
 *
 * `userAgent` and `platform` are `NavigatorID`'s getters answering the user
 * agent string and the platform's name, strings. */
export const navigatorMarker = "dom:navigator";
const navigatorIdentity = domIdentity("Navigator");
export const navigatorType: TypeTerm = named(navigatorIdentity);
const navigatorDefinition = definitionOf(navigatorIdentity, { k: "object", stringIndex: null, calls: [],
  host: navigatorMarker, span: at, fields: [field("userAgent", atom("string")), field("platform", atom("string"))] });

export const definitions: { bytes: TypeDefinition; buffer: TypeDefinition; bigIntStats: TypeDefinition;
  dirent: TypeDefinition; textDecoder: TypeDefinition; url: TypeDefinition; segmenter: TypeDefinition;
  segments: TypeDefinition; textMetrics: TypeDefinition; canvasContext: TypeDefinition; canvas: TypeDefinition;
  element: TypeDefinition; document: TypeDefinition; navigator: TypeDefinition; computedStyle: TypeDefinition; inlineStyle: TypeDefinition; htmlElement: TypeDefinition; dateTimeFormat: TypeDefinition } = {
  bytes: bytesDefinition, buffer: bufferDefinition, bigIntStats: bigIntStatsDefinition, dirent: direntDefinition,
  textDecoder: textDecoderDefinition, url: urlDefinition, segmenter: segmenterDefinition, segments: segmentsDefinition,
  textMetrics: textMetricsDefinition, canvasContext: canvasContextDefinition, canvas: canvasDefinition,
  element: elementDefinition, document: documentDefinition, navigator: navigatorDefinition,
  computedStyle: computedStyleDefinition, inlineStyle: inlineStyleDefinition, htmlElement: htmlElementDefinition,
  dateTimeFormat: dateTimeFormatDefinition };

/** The overlay's definitions a definition names, which join the document
 * with it: a `Buffer`'s `set` takes any view, a segmenter's `segment`
 * returns a `Segments`, whose iteration yields `SegmentData`, a context's
 * `measureText` returns a `TextMetrics`, a canvas's `getContext` a context,
 * and the document's members an element and a canvas. */
export function namedDefinitions(definition: TypeDefinition): TypeDefinition[] {
  return definition === bufferDefinition ? [bytesDefinition]
    : definition === segmenterDefinition ? [segmentsDefinition]
    : definition === segmentsDefinition ? [segmentDataDefinition]
    : definition === canvasContextDefinition ? [textMetricsDefinition]
    : definition === canvasDefinition ? [canvasContextDefinition]
    : definition === documentDefinition ? [elementDefinition, canvasDefinition, htmlElementDefinition, spanElementDefinition]
    : definition === spanElementDefinition ? [elementDefinition, inlineStyleDefinition]
    : definition === htmlElementDefinition ? [elementDefinition, inlineStyleDefinition]
    : definition === elementDefinition ? [rectangleDefinition] : [];
}

const node = "@types/node";
const library = "library";
/** Whether a type term names a view of bytes: a reference to the
 * declaration of a definition an entry of the overlay states as one
 * (`TypeEntry.view`). */
export function namesView(t: TypeTerm): boolean {
  if (t.k !== "reference") return false;
  const target = t.reference.target;
  return typesOverlay.some(e => e.view === "bytes" &&
    e.definition.declaration.module === target.module && e.definition.declaration.name === target.name);
}

export const typesOverlay: readonly TypeEntry[] = [
  { name: "HTMLSpanElement", definition: htmlElementDefinition, parts: [{ origin: library, heading: "interface HTMLSpanElement extends HTMLElement {" }] },
  { name: "CSSStyleDeclaration", definition: computedStyleDefinition, parts: [
    { origin: library, heading: "interface CSSStyleDeclaration extends CSSStyleProperties {" },
    { origin: library, heading: "interface CSSStyleDeclaration {" }] },
  { name: "DateTimeFormat", definition: dateTimeFormatDefinition, parts: [{ origin: library, heading: "interface DateTimeFormat {" }] },
  // The standard library's `Uint8Array`, as the configured standard library
  // declares it in parts, and Node's part adding `at`.
  { name: "Uint8Array", definition: bytesDefinition, view: "bytes", parts: [
    { origin: library, heading: "interface Uint8Array<TArrayBuffer extends ArrayBufferLike = ArrayBufferLike> {" },
    { origin: library, heading: "interface Uint8Array<TArrayBuffer extends ArrayBufferLike> {" },
    { origin: node, heading: "interface Uint8Array extends RelativeIndexable<number> {" }] },
  // The standard library's `Uint16Array`, `Int32Array` and `Float64Array`,
  // as it declares them in parts: views of bytes, at the type a
  // `Uint8Array` is.
  ...["Uint16Array", "Int32Array", "Float64Array"].map((name): TypeEntry => ({ name, definition: bytesDefinition, view: "bytes", parts: [
    { origin: library, heading: `interface ${name}<TArrayBuffer extends ArrayBufferLike = ArrayBufferLike> {` },
    { origin: library, heading: `interface ${name}<TArrayBuffer extends ArrayBufferLike> {` }] })),
  { name: "Buffer", definition: bufferDefinition, view: "bytes", parts: [
    { origin: node, heading: "interface Buffer<TArrayBuffer extends ArrayBufferLike = ArrayBufferLike> extends Uint8Array<TArrayBuffer> {" },
    { origin: node, heading: "interface Buffer {" }] },
  { name: "BigIntStats", definition: bigIntStatsDefinition, parts: [
    { origin: node, heading: "export interface BigIntStats extends StatsBase<bigint> {" }] },
  { name: "Dirent", definition: direntDefinition, arguments: [atom("string")], parts: [
    { origin: node, heading: "export class Dirent<Name extends string | Buffer = string> {" },
    { origin: node, heading: "export class Dirent {" }] },
  // Node's global `URL`, an interface extending the module's class, as both
  // pinned installations declare it.
  { name: "URL", definition: urlDefinition, parts: [{ origin: node, heading: "interface URL extends _URL {" }] },
  // The standard library's `Intl.Segmenter`, `Intl.Segments` and
  // `Intl.SegmentData`, each one interface of the namespace `Intl`, read by
  // their qualified names.
  { name: "Segmenter", definition: segmenterDefinition, parts: [{ origin: library, heading: "interface Segmenter {" }] },
  { name: "Segments", definition: segmentsDefinition, parts: [{ origin: library, heading: "interface Segments {" }] },
  { name: "SegmentData", definition: segmentDataDefinition, parts: [{ origin: library, heading: "interface SegmentData {" }] },
  // The DOM library's 2D contexts, one type, a `TextMetrics`, and the two
  // canvases a context is made from, one type.
  { name: "CanvasRenderingContext2D", definition: canvasContextDefinition, parts: [{ origin: library, heading:
    "interface CanvasRenderingContext2D extends CanvasCompositing, CanvasDrawImage, CanvasDrawPath, CanvasFillStrokeStyles, " +
    "CanvasFilters, CanvasImageData, CanvasImageSmoothing, CanvasPath, CanvasPathDrawingStyles, CanvasRect, CanvasSettings, " +
    "CanvasShadowStyles, CanvasState, CanvasText, CanvasTextDrawingStyles, CanvasTransform, CanvasUserInterface {" }] },
  { name: "OffscreenCanvasRenderingContext2D", definition: canvasContextDefinition, parts: [{ origin: library, heading:
    "interface OffscreenCanvasRenderingContext2D extends CanvasCompositing, CanvasDrawImage, CanvasDrawPath, " +
    "CanvasFillStrokeStyles, CanvasFilters, CanvasImageData, CanvasImageSmoothing, CanvasPath, CanvasPathDrawingStyles, " +
    "CanvasRect, CanvasShadowStyles, CanvasState, CanvasText, CanvasTextDrawingStyles, CanvasTransform {" }] },
  { name: "TextMetrics", definition: textMetricsDefinition, parts: [{ origin: library, heading: "interface TextMetrics {" }] },
  { name: "OffscreenCanvas", definition: canvasDefinition, parts: [
    { origin: library, heading: "interface OffscreenCanvas extends EventTarget {" }] },
  { name: "HTMLCanvasElement", definition: canvasDefinition, parts: [
    { origin: library, heading: "interface HTMLCanvasElement extends HTMLElement {" }] },
  { name: "Element", definition: elementDefinition, parts: [{ origin: library, heading:
    "interface Element extends Node, ARIAMixin, Animatable, ChildNode, NonDocumentTypeChildNode, ParentNode, Slottable {" }] },
  { name: "HTMLElement", definition: htmlElementDefinition, parts: [{ origin: library, heading:
    "interface HTMLElement extends Element, ElementCSSInlineStyle, ElementContentEditable, GlobalEventHandlers, HTMLOrSVGElement {" }] },
];

/** The entry stating `name`, where every part TypeScript binds it to as a
 * type is one of the entry's, exactly as reviewed; null where no entry names
 * it or none of the parts is one it reviews (another type of that name, a
 * program's). A name with a part the entry reviews and one whose origin or
 * heading it does not, a declaration merged into it among them, is
 * refused. */
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
