import type { CallEffect, ArrayPresence } from "./type-graph.mts";
/** The declaration document shared by the source parser, the Fragment AST
 * and readers. TypeScript's checker, under the source's configured project,
 * decides which declaration each name denotes; the document records the source
 * equations of the declarations reached. They are not evidence that a
 * producer's claim follows from them. This module has no runtime dependencies,
 * so importing its types does not pull the compiler into a reader's project. */
import type { Span } from "./span.mts";
/** One type alias or interface: its module (a path relative to the project's
 * tsconfig, the client's absolute path, or `typescript/lib/<file>`), its name
 * and its span there. */
export type DeclarationIdentity = {
  module: string;
  name: string;
  span: Span;
};
/** A property key: a string, or the symbol a `unique symbol` constant
 * denotes, by its index in the document's `symbols`. */
export type PropertyKey = string | { symbol: number };
/** A qualified source parameter owns the hidden projections of its
 * descriptor: its observation, and, where it is resolvable, its result (`null`
 * for an awaitable parameter). Their names are lexical binders, never source
 * type arguments. */
export type ResolutionSlots = { observation: string; result: string | null };
export type SourceTypeParameter<T> = {
  name: string;
  bound: T | null;
  resolution: ResolutionSlots | null;
};
/** A name the client binds to a declaration: an imported name (the span is
 * the import declaration's), one of the client's own declarations, or a
 * global the client names without importing it, such as the standard
 * library's `Promise` (the span is its first reference). */
export type TypeRoot = {
  binding:
    | { kind: "import"; local: string; imported: string; specifier: string; span: Span }
    | { kind: "local"; local: string; span: Span }
    | { kind: "global"; local: string; span: Span };
  declaration: DeclarationIdentity;
};
/** A reference inside a declaration, with the declaration TypeScript resolves it to. */
export type Reference = {
  name: string;
  span: Span;
  arguments: Span[];
  target: DeclarationIdentity;
};
/** A source type before translation to the positive graph: a declaration's
 * equation or a function annotation, read by type-term.mts. */
export type TypeTerm =
  /** `object` is every object: an ordinary one, an array, or one with call or
   * construct code. */
  | { k: "atom"; name: "null" | "undefined" | "boolean" | "number" | "string" | "bigint" | "symbol" | "unknown" | "never" | "void" | "object"; span: Span }
  /* A number's `text` is its decimal spelling, a bigint's its canonical
     decimal integer; either may be negative. */
  | { k: "literal"; name: "true" | "false" | "string" | "number" | "bigint"; text: string; span: Span }
  /** A `unique symbol` type: the one symbol the `symbol`-th listed `unique
   * symbol` declaration holds, as the symbol key `{ symbol }` names it. */
  | { k: "unique"; symbol: number; span: Span }
  | { k: "union" | "intersection"; parts: TypeTerm[]; span: Span }
  | { k: "array"; presence: ArrayPresence; readonly: boolean; element: TypeTerm; span: Span }
  | { k: "tuple"; presence: ArrayPresence; readonly: boolean; required: TypeTerm[];
      optional: TypeTerm[]; rest: TypeTerm | null; span: Span }
  /** `prototype`, stated by the library overlay only: members the object
   * holds as own properties that are not enumerable (an `Error`'s
   * `message`), which the model holds on a prototype it gives the object, so
   * that a spread does not copy them and `in` and reads still find them. */
  | { k: "object"; fields: { name: PropertyKey; optional: boolean; readonly: boolean; type: TypeTerm; span: Span }[];
      stringIndex: { readonly: boolean; value: TypeTerm; span: Span } | null;
      /** A number index, `[k: number]: V` with a contract of its own: it
       * constrains the canonical numeric keys ("0", "1.5", "-1", "NaN"),
       * present only when the object has one; likewise a symbol index, every
       * symbol key. */
      numberIndex?: { readonly: boolean; value: TypeTerm; span: Span };
      symbolIndex?: { readonly: boolean; value: TypeTerm; span: Span };
      calls: Extract<TypeTerm, { k: "function" }>[]; span: Span; prototype?: TypeTerm }
  | { k: "function"; effect: CallEffect; receiver: TypeTerm | null; params: TypeTerm[];
      rest: TypeTerm | null; result: TypeTerm; span: Span }
  /** `new (params) => result`: a construct signature, which a class meets and
   * no plain function does; `rest` as a function's, or null. A class value's
   * type also states its static fields (`statics`), own data properties of
   * the class value, a readonly one marked, left out when it has none. */
  | { k: "constructor"; params: TypeTerm[]; rest: TypeTerm | null; result: TypeTerm;
      statics?: { name: PropertyKey; type: TypeTerm; readonly?: true }[]; span: Span }
  /** A rest parameter typed by a type parameter, `...params: P`: the actuals
   * past the fixed ones are, as one argument list, at `P`, a pack parameter.
   * Only a signature's `rest` holds one; any other rest is its element. */
  | { k: "pack"; of: TypeTerm; span: Span }
  /** A generic method, `m<U>(f: (x: T) => U): Box<U>`, or a generic function
   * or constructor type: its binders, which its signatures name as `binder`
   * terms by spelling, and its signatures, call signatures (a method's with
   * the containing declaration as receiver) or construct signatures. A bound or default is stated
   * as written; which bounds are admitted is the reader's decision. */
  | { k: "scheme"; binders: (SourceTypeParameter<TypeTerm> & { default: TypeTerm | null;
      span: Span })[]; signatures: Extract<TypeTerm, { k: "function" | "constructor" }>[];
      span: Span }
  /** A value with call or construct code, of which no signature is known:
   * the meaning of the standard library's `Function` (PROGRAM-TYPING.md,
   * "Library types"). Nothing may be called or constructed through it. */
  | { k: "callable"; span: Span }
  /** The containing declaration is the implicit receiver of a method
   * signature; a method's `this: T` makes the receiver its intersection with
   * `T`, a type the host must meet. */
  | { k: "self"; span: Span }
  | { k: "parameter"; index: number; span: Span }
  /** A type parameter by its spelling: an enclosing function's, in an
   * annotation, or a generic method's, in its scheme. A declaration's own
   * parameters are positional. */
  | { k: "binder"; name: string; span: Span }
  | { k: "reference"; reference: Reference; args: TypeTerm[]; span: Span };
export type TypeDefinition = {
  declaration: DeclarationIdentity;
  parameters: { name: string; span: Span; bound: TypeTerm | null;
    default: TypeTerm | null }[];
  /** Interface heritage remains a source edge; consumers derive its members. */
  bases: TypeTerm[];
  expression: TypeTerm;
};
/** Every declaration reachable from the roots, each once. References live in
 * the expression, parameter bounds/defaults and heritage edges, not in a second list. */
/** A value the client imports: the declaration TypeScript resolves it to, and
 * the type that declaration states. A function is its annotated signature, a
 * constant its annotation, and a class its constructor, which only `new`
 * calls. A global variable the client reads, such as `process`, is listed
 * the same way, with the specifier `global`, at a definition keyed by its
 * declaration that holds the members the client selects (PROGRAM-TYPING.md,
 * "Imported, ambient and global values"). Nothing here checks the imported code: each is an assumption the
 * client's result is relative to. */
export type ValueRoot = {
  binding: { local: string; imported: string; specifier: string; span: Span };
  declaration: DeclarationIdentity;
  construct: boolean;
  /** A generic declaration's binders, which `type` names as `binder` terms. */
  typeParams: SourceTypeParameter<TypeTerm>[];
  type: TypeTerm;
};
export type DeclarationDocument = {
  roots: TypeRoot[];
  definitions: TypeDefinition[];
  values: ValueRoot[];
  /** The `unique symbol` constants the definitions use as property keys, each
   * once: distinct declarations are distinct symbols, as TypeScript assumes. */
  symbols: DeclarationIdentity[];
};
