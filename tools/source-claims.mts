/*
 * The claims document, described in TypeScript.
 *
 * A producer states, for one source file, what it believes at every site the
 * lowering visits; the verifier asks whether those beliefs are derivable.
 * SOURCE-CLAIMS.md specifies the format in prose. The OCaml producer
 * (`ocaml-producer/claims.ml`) writes the document and the verifier's Lean
 * decoder (`Claims/Wire.lean`) reads it, requiring every field and refusing
 * any other. This description types the pipeline's TypeScript code that
 * reads a document the producer wrote, or forges one in a control
 * (`readClaimsFile` in `pipeline/verify-source.mts`, which checks the JSON is
 * well formed and decodes no field). It is tied to the writer and the reader
 * by field names only (`tests/json-field-names.mts`): a shape that differs
 * under the same names is reported where Lean decodes a document, and no
 * check compares the producer's output with these types.
 */

import type { Span } from "./span.mts";
import type { CallEffect, ClosedFootprint, Labels, Row } from "./type-graph.mts";
import type { DeclarationIdentity, PropertyKey, SourceTypeParameter } from "./declaration-types.mts";
export type { Row } from "./type-graph.mts";

/** A label: a row of the document's own `types`, or a tree naming a row
 * the producer does not build, which Lean builds from the declaration
 * document. An application names its declaration by position in
 * `definitions`, with one argument per parameter, `args` left out for a
 * nullary one; an intersection has at least two parts; an array names its
 * store's one row; a binder is one in scope, by name. A label list is in
 * canonical order (SOURCE-CLAIMS.md, "Encoding"). */
type Label =
  | number
  | { decl: number; args?: Label[][] }
  | { meet: Label[][] }
  | { array: Label[]; readonly: boolean }
  | { binder: string };
/*
 * Every type below is generic in its label, the wire's `Label` by default; a
 * document whose labels are all rows of its own table is the `number`
 * instance.
 */

/** A quantified callable. Parameter references inside it are resolved
 * lexically: its binders shadow enclosing binders only within this value. */
interface SchemeClaim<L = Label> {
  effect: CallEffect;
  typeParams: SourceTypeParameter<ClaimType<L>>[];
  /** The receiver a call passes; an unknown row when any is accepted. */
  this: ClaimType<L>;
  params: ClaimType<L>[];
  rest: ClaimType<L> | null;
  result: ClaimType<L>;
}

/** Ground graph labels, a lexically scoped rigid parameter, their union, or a quantified
 * callable. This is the one type language shared by every producer. */
type ClaimType<L = Label> =
  | Labels<L>
  | { param: string }
  | { array: ClaimType<L> }
  | { union: ClaimType<L>[] }
  | { scheme: SchemeClaim<L> }
  | { unavailable: string };

/**
 * What a producer believes at one site: the type it claims, and — where the
 * site names a record and the producer tracks its contents — what each named
 * field holds at that point. An object has one location per field, so the
 * assertion names the field it is about, or the path of fields read in turn
 * from the point's value, a path of two or more only at a statement entry
 * (HOST-FAMILIES.md, "Entries"). `current` is required and explicitly `null`
 * where no such assertion is made, so silence is stated rather than inferred.
 */
type CurrentFields<L = Label> = [fields: [PropertyKey, ...PropertyKey[]], labels: Labels<L>][];

interface Point<L = Label> {
  type: ClaimType<L>;
  current: CurrentFields<L> | null;
}

/** A named point: a parameter, or a binding visible at a statement entry. */
interface NamedPoint<L = Label> extends Point<L> {
  name: string;
}

/** The environment at one shared control-flow point, with source provenance. */
interface EntryClaim<L = Label> {
  point: string;
  start: number;
  bindings: NamedPoint<L>[];
}

/** The type arguments one call supplies for a scheme's binders. It records the
 * elimination a producer proposes; the verifier re-checks it against the
 * scheme's signature and never infers one of its own. Absent at every site that
 * is not a call to a quantified callable. */
interface TypeArgument<L = Label> {
  name: string;
  type: ClaimType<L>;
  resolution: { certificate: ResolutionCertificate } | null;
}
/** Finite descriptor construction, checked against the complete input type. */
type ResolutionCertificate =
  | { k: "stable" }
  | { k: "native"; child: ResolutionCertificate }
  | { k: "promise" }
  | { k: "union"; arms: ResolutionCertificate[] }
  | { k: "binder"; binder: string };

interface ExpressionClaim<L = Label> extends Point<L> {
  point: string;
  pos: Span;
  instantiate?: TypeArgument<L>[] | null;
}

/** The fixed storage contract of a mutable declaration. */
interface StorageContract<L = Label> {
  pos: Span;
  name: string;
  type: ClaimType<L>;
}

/** The claims of a unit's body: what a function's claims and the module
 * initialization unit's share. */
interface BodyClaims<L = Label> {
  contracts: StorageContract<L>[];
  entries: EntryClaim<L>[];
  expressions: ExpressionClaim<L>[];
  /** One interior claim set per advertised signature of the closure at pos. */
  arrows?: {
    pos: Span;
    rows: { contracts: StorageContract<L>[]; expressions: ExpressionClaim<L>[]; entries: EntryClaim<L>[] }[];
  }[];
}

interface FunctionClaims<L = Label> extends BodyClaims<L> {
  name: string;
  namePos: Span;
  params: NamedPoint<L>[];
  result: ClaimType<L>;
  /** The footprint proposed for the declaration's signature, which its
   * unit's graph must establish. */
  footprint: ClosedFootprint;
  /** Whether the footprint is proposed on a throw too, which the unit's
   * graph must establish as well. */
  onThrow: boolean;
}

export interface SourceClaims<L = Label> {
  file: string;
  sourceSha256: string;
  /** The producer's rows: the four primitives, then its own clause rows. */
  types: Row<L>[];
  functions: FunctionClaims<L>[];
  /** The module initialization unit, present exactly when the source has
   * top-level code: its entries and expressions, with no parameters. */
  init?: BodyClaims<L>;
  /** Claims documents of fragment modules, each a module run's own, over
   * its own rows, its `modules` and `qualified` empty. */
  modules: SourceClaims<L>[];
  /** The imports read qualified (certified imports), each by its
   * declaration identity. */
  qualified: DeclarationIdentity[];
}
