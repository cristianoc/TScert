/*
 * The producer-independent claims document, described once.
 *
 * A producer states, for one source file, what it believes at every site the
 * lowering visits; the verifier asks whether those beliefs are derivable.
 * SOURCE-CLAIMS.md specifies the format in prose; this is the same thing for
 * the tools that write and read it, so the producer and the consumer cannot
 * drift apart silently. A document either has exactly this shape, which every
 * decoder requires field by field, or it is rejected.
 */

import type { Span } from "./span.mts";
import type { CallEffect, Labels, Row } from "./type-graph.mts";
import type { SourceTypeParameter } from "./declaration-types.mts";
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
 * Every type below is generic in its label, the wire's `Label` by default. A
 * producer that names only rows of its own table, as the tsc producer does,
 * writes the `number` instance, and a reader of such a
 * document reads that instance.
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
 * assertion names the field it is about. `current` is required and explicitly
 * `null` where no such assertion is made, so silence is stated rather than
 * inferred.
 */
type CurrentFields<L = Label> = [name: string, labels: Labels<L>][];

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

interface FunctionClaims<L = Label> {
  name: string;
  namePos: Span;
  params: NamedPoint<L>[];
  result: ClaimType<L>;
  contracts: StorageContract<L>[];
  entries: EntryClaim<L>[];
  expressions: ExpressionClaim<L>[];
  /** One interior claim set per advertised signature of the closure at pos. */
  arrows?: {
    pos: Span;
    rows: { contracts: StorageContract<L>[]; expressions: ExpressionClaim<L>[]; entries: EntryClaim<L>[] }[];
  }[];
}

export interface SourceClaims<L = Label> {
  file: string;
  sourceSha256: string;
  /** The producer's rows: the four primitives, then its own clause rows. */
  types: Row<L>[];
  functions: FunctionClaims<L>[];
  /** The module initialization unit, present exactly when the source has
   * top-level code: its entries and expressions, with no parameters. */
  init?: Pick<FunctionClaims<L>, "contracts" | "entries" | "expressions" | "arrows">;
}
