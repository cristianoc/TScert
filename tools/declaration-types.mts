import type { ArrayPresence, ViewFormat } from "./type-graph.mts";
/** The declaration document shared by the source parser, the Fragment AST
 * and readers. TypeScript's checker, under the source's configured project,
 * decides which declaration each name denotes; the document records the source
 * equations of the declarations reached. They are not evidence that a type
 * stated at a point follows from them. This module has no runtime dependencies,
 * so importing its types does not pull the compiler into a reader's project. */
import type { Span } from "./span.mts";
/** A closed footprint (`Footprints.Closed`): the change a call may make, on
 * normal return, to the locations of its entry heap holding a value and to
 * those holding a spine, an array's or a view spine. `keep` changes nothing,
 * `extend` appends fresh cells at an array spine's end and keeps a view
 * spine, `grow` keeps every dense prefix of a spine, `any` allows every
 * change; on a value `extend` and `grow` are `scalar`, on a spine `init` and
 * `scalar` are `keep`. Fresh locations are unconstrained. */
export type ClosedFootprint = { readonly value: "keep" | "init" | "scalar" | "any"; readonly spine: "keep" | "extend" | "grow" | "any" };
/** A promise about the actual at `param`, whose type is then the signature's
 * result: a type guard's or an assertion function's. */
export type CallPromise = { readonly guards: { readonly param: number }; readonly asserts?: never } |
  { readonly asserts: { readonly param: number }; readonly guards?: never };
/** A location's permitted change (`Footprints.Change`). */
export type Change = "keep" | "init" | "scalar" | "extend" | "grow" | "any";
/** A property key: a string, or a symbol by its identity (`PropKey`). */
export type Key = string | { readonly symbol: number };
/** The content categories a class region selects (`Footprints.Selector`). */
export type Selector = { readonly value: boolean; readonly array: boolean; readonly view: boolean };
/** A region of locations, read at the call's entry (`Footprints.Region`):
 * a field, the fields or the cells of the value at position
 * `x`, a content class, every location, the same through the data fields
 * `fields`, a region within a class, and the spine the
 * value through `fields` selects. */
export type Region =
  | { readonly field: { readonly x: number; readonly key: Key } }
  | { readonly fields: { readonly x: number } }
  | { readonly cells: { readonly x: number } }
  | { readonly cls: Selector }
  | "all"
  | { readonly path: { readonly x: number; readonly fields: readonly string[]; readonly key: Key } }
  | { readonly pathFields: { readonly x: number; readonly fields: readonly string[] } }
  | { readonly pathCells: { readonly x: number; readonly fields: readonly string[] } }
  | { readonly inCls: { readonly region: Region; readonly selector: Selector } }
  | { readonly spine: { readonly x: number; readonly fields: readonly string[] } };
/** A frame: the regions an exit may change, each with its change
 * (`Footprints.Footprint`). */
export type Frame = readonly { readonly region: Region; readonly change: Change }[];
/** A path: a root position and the data fields read from its value. */
export type Path = { readonly root: number; readonly fields: readonly string[] };
/** A primitive constant of a specification: a number by its double's bits
 * (sixteen lowercase hexadecimal digits), a bigint by its decimal text, a
 * symbol by its identity. */
export type Literal = "null" | "undefined" | "true" | "false"
  | { readonly num: { readonly bits: string } } | { readonly str: { readonly value: string } }
  | { readonly bigint: { readonly value: string } } | { readonly sym: { readonly id: number } };
/** A path or a literal (`Parity.Witness`). */
export type Witness = { readonly path: Path } | { readonly literal: Literal };
/** A sequence of a call's values: fixed witnesses, the actuals from call
 * position `first` on, or two in turn (`WitnessSeq`). */
export type WitnessSeq =
  | { readonly fixed: { readonly xs: readonly Witness[] } }
  | { readonly restFrom: { readonly first: number } }
  | { readonly append: { readonly left: WitnessSeq; readonly right: WitnessSeq } };
/** The names of the entry read at the exit: entry slot `i` is exit slot
 * `i + shift` but for the first override of `i`; with `boxed`, an image
 * reading the heap holds only at a `stable` slot (`TransportSchema`). */
export type TransportSchema = { readonly shift: number; readonly overrides: readonly (readonly [number, Witness])[];
  readonly boxed: boolean; readonly stable: readonly number[] };
/** A two-state variable: a term read at the entry or at the exit. */
export type StepVar = { readonly before: { readonly t: LinearTerm } } | { readonly after: { readonly t: LinearTerm } };
/** A binary operator of the calculus by its name (`Arith`). */
export type Arith = "add" | "sub" | "mul" | "div" | "pow" | "xor" | "rem" | "bitAnd" | "bitOr" | "shl" | "shr" |
  "ushr" | "lt" | "le" | "gt" | "ge" | "eq" | "looseEq";
/** An operational postcondition (`Parity.OperationPostF`): `x` an entry
 * position and `exit` an exit position, freshness and `elementsWhen` at exit
 * positions, a fact at its phase's positions raised by `lift`. */
export type OperationPost =
  | { readonly arith: { readonly op: Arith; readonly left: Witness; readonly right: Witness; readonly result: Path } }
  | { readonly stringLength: { readonly string: Path; readonly result: Path } }
  | { readonly stringRead: { readonly string: Path; readonly index: Witness; readonly result: Path } }
  | { readonly lengthsKept: { readonly x: number; readonly exit: number } }
  | { readonly boundedWrite: { readonly x: number; readonly i: number; readonly exit: number } }
  | { readonly push: { readonly x: number; readonly exit: number; readonly args: WitnessSeq } }
  | { readonly fact: { readonly phase: "before" | "after"; readonly lift: number; readonly fact: IndexFact } }
  | { readonly freshSpine: { readonly x: number } }
  | { readonly freshObject: { readonly x: number } }
  | { readonly elementsWhen: { readonly x: number; readonly value: Literal; readonly y: number;
      readonly predicate: ElementKinds } }
  | { readonly spineExtends: { readonly x: number } }
  | { readonly viewWrite: { readonly x: number; readonly i: number; readonly v: number; readonly format: ViewFormat | null } };
/** A two-state postcondition of a specification
 * (`FormulaF WitnessSeq TransportSchema`, no assertion-arena node). */
export type Formula =
  | { readonly transition: { readonly effect: Frame } }
  | { readonly operation: { readonly post: OperationPost } }
  | { readonly linear: { readonly fact: LinearFactOf<StepVar> } }
  | { readonly defined: { readonly v: StepVar } }
  | { readonly transport: TransportSchema }
  | { readonly and: { readonly left: Formula; readonly right: Formula } }
  | "truth" | "falsity";
/** An exit's guarantee: the frame of the old locations it may change and
 * its postconditions (`ExitSchema`). */
export type ExitSchema = { readonly frame: Frame; readonly ensures: readonly Formula[] };
/** One datum per completion of a call (`Exits`). */
export type Exits<A> = { readonly normal: A; readonly exceptional: A };
/** **A callable's effect** (`CallEffects.Effect`, REQUEST-PROTOCOL.md, "The
 * serialized effect"): its two exits, a normal return's and a throw's,
 * read at the call's entry positions (`0` the receiver, `i + 1` the `i`-th
 * actual) and at the exit's (`0` the returned or thrown value, `1` the
 * receiver, `i + 2` the `i`-th actual); an optional promise; a precondition
 * on the receiver's elements; and preconditions on the call's values. */
export type CallEffect = {
  readonly exits: Exits<ExitSchema>;
  readonly promise: CallPromise | null;
  readonly requires: ElementKinds | null;
  readonly pre: readonly IndexFact[];
};
/** What a typed array's element write keeps (`CallEffects.ElementWrite`):
 * every location holding no spine and every spine's length (`"spines"`);
 * besides, for an element assignment `b[i] = v` (`"assign"`), the write of
 * the element at the view's own format (`CallEffects.ViewAssign`, the
 * note's View-Write for every number) and the value as the result; and
 * besides, for a view of the named element type at position 1, the
 * element at the index at position 2 holds that type's conversion of the
 * value at position 3 (`CallEffects.ElementKind.convert`: the number
 * denoting the value's integer for an integer type, the value itself for
 * `Float64Array`), its other elements unchanged (`"exactUint8"`,
 * `"exactUint16"`, `"exactInt32"`, `"exactFloat64"`). An authoring option of
 * `footprintEffect`, which states it as postconditions. */
export type ElementWrite = "spines" | "assign" | ExactElementWrite;
/** The exact element write of each element type (`ElementWrite`). */
export type ExactElementWrite = "exactUint8" | "exactUint16" | "exactInt32" | "exactFloat64";
/** An index fact at numbered positions (`HeapKnowledge.IndexFact`, its
 * constructor's name holding its fields): an array index; the length of an
 * array's spine; an index at most that length, below it where `strict`; a
 * safe integer; the double `2^53`, past the safe integers (`pastSafe`); a linear fact `Σ c·t ≤ d` or `≠ d`; a guarded fact, which
 * holds where the named data fields `path` read from the position `slot`
 * give the value `tag` names, or where its body holds (ARITHMETIC.md,
 * "Guarded clauses"); the value at position `value` is what the array at
 * `array` holds at the index at `index`, below its length (`element`); for
 * every index `i` with `0 ≤ i < stop` of the array the path `path` reads from
 * the position `slot`, each body fact holds of `i`, the element at it and its
 * terms (`every`, ARITHMETIC.md, "Quantified clauses"). */
export type IndexFact =
  | { readonly index: { readonly slot: number } }
  | { readonly length: { readonly array: number; readonly length: number } }
  | { readonly bound: { readonly array: number; readonly index: number; readonly strict: boolean } }
  | { readonly int: { readonly slot: number } }
  | { readonly pastSafe: { readonly slot: number } }
  | { readonly linear: { readonly fact: LinearFact } }
  | { readonly either: { readonly left: IndexFact; readonly right: IndexFact } }
  | { readonly guarded: { readonly slot: number; readonly path: readonly string[]; readonly tag: GuardTag;
      readonly body: IndexFact } }
  | { readonly element: { readonly value: number; readonly array: number; readonly index: number } }
  | { readonly every: { readonly slot: number; readonly path: readonly string[]; readonly stop: LinearTerm;
      readonly body: readonly BodyFact[] } }
  | { readonly apart: { readonly slot: number; readonly other: number } }
  | { readonly spineApart: { readonly slot: number; readonly path: readonly string[]; readonly other: number;
      readonly otherPath: readonly string[] } };
/** A variable of a quantified fact's body (`HeapKnowledge.Bound`): the bound
 * index, the element at it, or a linear term. */
export type BodyVariable = "index" | "elem" | { offset: { delta: number } } | { readonly project: { readonly kind: LinearTerm["kind"]; readonly path: readonly string[] } } | { readonly free: { readonly t: LinearTerm } };
/** A linear fact of a quantified fact's body, over its variables. */
export type BodyFact =
  | { readonly either: { readonly left: BodyFact; readonly right: BodyFact } }
  | { readonly le: { readonly form: readonly (readonly [BodyVariable, Integer])[]; readonly bound: Integer } }
  | { readonly ne: { readonly form: readonly (readonly [BodyVariable, Integer])[]; readonly bound: Integer } };
/** The value a guard compares a path's read with (`HeapKnowledge.GuardTag`). */
export type GuardTag = "null" | "undefined" | "true" | "false";
/** A linear fact (`Linear.Fact`): `Σ c·t ≤ bound` or `≠ bound`, each term a
 * linear term and its coefficient. */
export type LinearFact = LinearFactOf<LinearTerm>;
/** An integer of a linear fact: a number in the safe range, its canonical
 * decimal string outside it (REQUEST-PROTOCOL.md, "The serialized effect"). */
export type Integer = number | string;
/** A linear fact over variables `V`. */
export type LinearFactOf<V> =
  | { readonly le: { readonly form: readonly (readonly [V, Integer])[]; readonly bound: Integer } }
  | { readonly ne: { readonly form: readonly (readonly [V, Integer])[]; readonly bound: Integer } };
/** A term of a linear fact (`HeapKnowledge.Term`): a root position, the
 * named data fields read from what it holds in turn (`path`, empty for the
 * position's own value), and what the term reads of the value the path ends
 * at (`kind`): the safe integer it is, the length of its array spine, the
 * length of the typed array it is, or the length of the string it is. */
export type LinearTerm = {
  readonly kind: "value" | "length" | "view" | "strLength";
  readonly slot: number;
  readonly path: readonly string[];
  /** An entry term `old(t)` of a postcondition (the note "Tolerant frames",
   * section 6): `t` read at the state the function started in, `slot` a
   * position of its entry. */
  readonly atEntry?: true;
};
/** The kinds of value an elements predicate admits (`CallEffects.ElemPred`),
 * each at most once, in this order. */
export type ElementKind = "null" | "undefined" | "boolean" | "number" | "string" | "bigint" | "symbol" | "object";
export type ElementKinds = readonly ElementKind[];
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
   * constructed. `safeInt` is the safe integers, the verifier's declared
   * type `SafeInt` (`resolvable.d.ts`). */
  | { k: "atom"; name: "null" | "undefined" | "boolean" | "number" | "safeInt" | "string" | "bigint" | "symbol" | "unknown" | "never" | "void" | "object" | "nonHost" | "nonHostObject" | "function" | "class"; span: Span }
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
      /** A typed array's element format, stated by the library overlay's
       * typed-array and `Buffer` readings only: the type is the typed arrays
       * of that format (Lean's `Clause.view`), values a view descriptor
       * makes typed arrays, and the object states their methods alone. */
      view?: ViewFormat;
      /** The required readonly members stated stable, never empty: a host
       * family's reading's (HOST-FAMILIES.md, "Stable keys"), or a program
       * record's members tagged `@stable` (POSITIVE-TYPES.md, "Records").
       * Each is owned at a location of one value. */
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
