import type { ArrayPresence } from "./type-graph.mts";
/** The declaration document shared by the source parser, the Fragment AST
 * and readers. TypeScript's checker, under the source's configured project,
 * decides which declaration each name denotes; the document records the source
 * equations of the declarations reached. They are not evidence that a
 * producer's claim follows from them. This module has no runtime dependencies,
 * so importing its types does not pull the compiler into a reader's project. */
import type { Span } from "./span.mts";
/** A closed footprint (`Footprints.Closed`): the change a call may make, on
 * normal return, to the locations of its entry heap holding a value and to
 * those holding an array store. `keep` changes nothing, `grow` keeps every
 * dense prefix of a store, `any` allows every change; on a value `grow` is
 * `keep`. Fresh locations are unconstrained. */
export type ClosedFootprint = { readonly value: "keep" | "any"; readonly store: "keep" | "grow" | "any" };
/** A promise about the actual at `param`, whose type is then the signature's
 * result: a type guard's or an assertion function's. */
export type CallPromise = { readonly guards: { readonly param: number }; readonly asserts?: never } |
  { readonly asserts: { readonly param: number }; readonly guards?: never };
/** What a signature guarantees beyond its contract: its footprint, an
 * optional promise, whether a normal return's value has an array store the
 * call allocated (`fresh`), and whether the footprint excepts the receiver's
 * array store, which the call may change arbitrarily (`receiverStore`), and
 * whether the footprint also bounds the heap a throw leaves (`onThrow`)
 * (`CallEffects.Effect`). */
export type CallEffect = {
  readonly footprint: ClosedFootprint; readonly promise: CallPromise | null; readonly fresh: boolean;
  readonly receiverStore: boolean; readonly onThrow: boolean;
  /** The footprint bounds every old location but the receiver's own ones. */
  readonly receiverOwn: boolean;
  /** A normal return's value is an object every own location of which the
   * call allocated. */
  readonly freshObject: boolean;
  /** A precondition: every present element of the receiver's array has one
   * of these kinds in the heap the call starts in. */
  readonly requires: ElementKinds | null;
  /** A promise: a normal return of `true` leaves every present element of
   * the receiver's array of one of these kinds. */
  readonly elements: ElementKinds | null;
  /** A precondition on the call's values: each index fact holds of them in
   * the heap the call starts in, read at the call's positions (0 the
   * receiver, i + 1 the i-th actual) (`CallEffects.Effect.pre`). */
  readonly pre: readonly IndexFact[];
  /** Result facts: each index fact holds in the heap a normal return leaves,
   * read at the return's positions (0 the result, i + 1 the call's position
   * i) (`CallEffects.Effect.ensures`). Only a trusted signature states one. */
  readonly ensures: readonly IndexFact[];
};
/** An index fact at numbered positions (`HeapKnowledge.IndexFact`, its
 * constructor's name holding its fields): an array index; the length of an
 * array's store; an index at most that length, below it where `strict`; a
 * safe integer; a linear fact `Σ c·t ≤ d` or `≠ d`; a guarded fact, which
 * holds where the named data fields `path` read from the position `slot`
 * give the value `tag` names, or where its body holds (PROGRAM-TYPING.md,
 * "Guarded clauses"). */
export type IndexFact =
  | { readonly index: { readonly slot: number } }
  | { readonly length: { readonly array: number; readonly length: number } }
  | { readonly bound: { readonly array: number; readonly index: number; readonly strict: boolean } }
  | { readonly int: { readonly slot: number } }
  | { readonly linear: { readonly fact: LinearFact } }
  | { readonly guarded: { readonly slot: number; readonly path: readonly string[]; readonly tag: GuardTag;
      readonly body: IndexFact } };
/** The value a guard compares a path's read with (`HeapKnowledge.GuardTag`). */
export type GuardTag = "null" | "undefined";
/** A linear fact (`Linear.Fact`): `Σ c·t ≤ bound` or `≠ bound`, each term a
 * linear term and its coefficient. */
export type LinearFact =
  | { readonly le: { readonly form: readonly (readonly [LinearTerm, number])[]; readonly bound: number } }
  | { readonly ne: { readonly form: readonly (readonly [LinearTerm, number])[]; readonly bound: number } };
/** A term of a linear fact (`HeapKnowledge.Term`): a root position, the
 * named data fields read from what it holds in turn (`path`, empty for the
 * position's own value), and what the term reads of the value the path ends
 * at (`kind`): the safe integer it is, the length of its array store, or the
 * element count of the typed array it is. */
export type LinearTerm = {
  readonly kind: "value" | "length" | "view";
  readonly slot: number;
  readonly path: readonly string[];
};
/** The kinds of value an elements predicate admits (`CallEffects.ElemPred`),
 * each at most once, in this order. */
export type ElementKind = "null" | "undefined" | "boolean" | "number" | "string" | "bigint" | "symbol" | "object";
export type ElementKinds = readonly ElementKind[];
/** The effect a written signature states at its result (`Within<F, T>`,
 * SOURCE-ELABORATION.md, "Stated effects"): a closed footprint and whether
 * it also bounds the heap a throw leaves. */
export type StatedEffect = { footprint: ClosedFootprint; onThrow: boolean };
/** One type alias or interface: its module, its name and its span there. The
 * module identities are disjoint by construction: the client's absolute
 * path; `typescript/lib/<file>` for a file the compiler's library resolution
 * gives the program, and no other; any other file's path from the project's
 * tsconfig, `./…` inside it and `../…` outside. A `typescript/lib/` module is
 * thus a standard library file, which the wire's readers rely on. */
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
   * construct code. `nonHost`, which no source spells and only the library
   * overlay states, is every value but a host object (COMPILER-API.md,
   * "Restricted values"): a primitive, a callable or an ordinary object.
   * `nonHostObject` is its ordinary-object arm, used for native allocation
   * results. `function` is every value with call code, of which no signature is
   * known, which no class value meets: a function type whose rest admits no
   * argument list, `(...args: never) => R`, through which nothing may be
   * called. `class` is every class value, of which no construct signature is
   * known: a constructor type whose rest admits no argument list,
   * `abstract new (...args: never) => R`, through which nothing may be
   * constructed. */
  | { k: "atom"; name: "null" | "undefined" | "boolean" | "number" | "string" | "bigint" | "symbol" | "unknown" | "never" | "void" | "object" | "nonHost" | "nonHostObject" | "function" | "class"; span: Span }
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
   * holds as own properties that are not enumerable or inherits (an
   * `Error`'s `message` and `name`), which the model holds on a prototype it
   * gives the object, so that a spread does not copy them and `in` and reads
   * still find them. */
  | { k: "object"; fields: { name: PropertyKey; optional: boolean; readonly: boolean; type: TypeTerm; span: Span }[];
      stringIndex: { readonly: boolean; value: TypeTerm; span: Span } | null;
      /** A number index, `[k: number]: V` with a contract of its own: it
       * constrains the canonical numeric keys ("0", "1.5", "-1", "NaN"),
       * present only when the object has one; likewise a symbol index, every
       * symbol key. */
      numberIndex?: { readonly: boolean; value: TypeTerm; span: Span };
      symbolIndex?: { readonly: boolean; value: TypeTerm; span: Span };
      calls: Extract<TypeTerm, { k: "function" }>[]; span: Span; prototype?: TypeTerm;
      /** A host family's marker (HOST-FAMILIES.md, "The family contract"),
       * stated by the family's reading only: the record also has a required
       * readonly view of the model's `[[host]]` at this string, which no
       * allocation of the program owns. */
      host?: string;
      /** The required readonly members a family's reading states stable
       * (HOST-FAMILIES.md, "Stable keys"), stated with `host` only, never
       * empty: each is owned at a location of one value. */
      stable?: string[] }
  | { k: "function"; effect: CallEffect; receiver: TypeTerm | null; params: TypeTerm[];
      rest: TypeTerm | null; result: TypeTerm; span: Span }
  /** `new (params) => result`: a construct signature, which a class meets and
   * no plain function does; `rest` as a function's, or null; its effect as a
   * function's. A class value's type also states its static fields
   * (`statics`), own data properties of the class value, a readonly one
   * marked, left out when it has none. */
  | { k: "constructor"; effect: CallEffect; params: TypeTerm[]; rest: TypeTerm | null; result: TypeTerm;
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
   * the meaning of the standard library's `Function` (SOURCE-CONTRACTS.md,
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
  /** Its type parameters, each with whether it has a default. Every
   * reference carries all its arguments, the omitted ones completed with the
   * defaults where the reference is read; a parameter's bound is read at each
   * written application (`WrittenApplication`). */
  parameters: { name: string; span: Span; defaulted: boolean }[];
  /** Interface heritage remains a source edge; consumers derive its members. */
  bases: TypeTerm[];
  /** The equation; null where none is read: an alias TypeScript computes
   * from its parameters, a declaration whose computed members are read at
   * closed instances, or a library type read at its meaning, stated for its
   * parameters. */
  expression: TypeTerm | null;
};
/** A type application written in source syntax, `D<σ⃗>`, which obliges
 * each argument, completed with the defaults, to meet its parameter's bound
 * at those arguments, in `scope`: binder groups from the outermost, each
 * binder named freshly (`name@module:offset`) and bounded by its assumption,
 * the arguments and bounds naming them by that name
 * (`written-applications.mts`). */
export type WrittenApplication = {
  scope: SourceTypeParameter<TypeTerm>[][];
  reference: Reference;
  /** The target's parameters, for diagnostics. */
  parameters: { name: string; span: Span }[];
  /** One per parameter: the argument written, or the default at the
   * earlier arguments. */
  args: TypeTerm[];
  /** One per parameter: its declared bound at the arguments (`B[X⃗ := σ⃗]`),
   * or null where it declares none. */
  bounds: (TypeTerm | null)[];
  /** Where it is written in the client file, or null elsewhere. */
  span: Span | null;
  /** The module and declaration it is written in, for diagnostics. */
  site: string;
};
/** Every declaration reachable from the roots, each once. References live in
 * the expression, parameter bounds/defaults and heritage edges, not in a second list. */
/** A value the client imports: the declaration TypeScript resolves it to, and
 * the type that declaration states. A function is its annotated signature, a
 * constant its annotation, and a class its constructor, which only `new`
 * calls. A global variable the client reads, such as `process`, is listed
 * the same way, with the specifier `global`, at a definition keyed by its
 * declaration that holds the members the client selects (SOURCE-CONTRACTS.md,
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
  /** Every type application written in the swept syntax whose target has a
   * bounded parameter: the client file's, and that of every user
   * declaration it reaches. */
  applications: WrittenApplication[];
};
