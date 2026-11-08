/*
 * The claims document, described in TypeScript.
 *
 * A producer states, for one source file, what it believes at every site the
 * lowering visits; the verifier asks whether those beliefs are derivable.
 * SOURCE-CLAIMS.md specifies the format in prose. The OCaml producer
 * (`ocaml-producer/claims.ml`) writes the document and the verifier's Lean
 * decoder (`Claims/Wire.lean`) reads it, requiring every field and refusing
 * any other. Every document the pipeline's producer writes is decoded against
 * this description (`decodeSourceClaims`, called by `pipeline/verify-source.mts`
 * on each run and by `readClaimsFile` for the controls that forge one), so a
 * field the producer writes otherwise fails the run. The field names are
 * compared with the producer's writes and Lean's reads by
 * `tests/json-field-names.mts`.
 */

import type { Span } from "./span.mts";
import type { CallEffect, ClosedFootprint, Labels, Row, SchemeRow } from "./type-graph.mts";
import { decodeCallEffect, decodeClosedFootprint, decodeRows } from "./type-graph.mts";
import { hasExactly, isJsonList, isJsonObject, type Json, type JsonObject, type JsonRead, type JsonValue } from "./calculus.mts";
import { requireWellFormed } from "./wire-strings.mts";
import type { DeclarationIdentity, PropertyKey, ResolutionSlots, SourceTypeParameter } from "./declaration-types.mts";
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
 * assertion names the field it is about, or the nonempty path of fields read
 * in turn from the point's value, a path of two or more only at a statement entry
 * (HOST-FAMILIES.md, "Entries"). `current` is required and explicitly `null`
 * where no such assertion is made, so silence is stated rather than inferred.
 */
type CurrentFields<L = Label> = [fields: PropertyKey[], labels: Labels<L>][];

interface Point<L = Label> {
  type: ClaimType<L>;
  current: CurrentFields<L> | null;
}

/** A named point: a parameter, or a binding visible at a statement entry. */
interface NamedPoint<L = Label> extends Point<L> {
  name: string;
}

/** A bound a guard states at a statement entry: the value `index` names is an
 * array index at most the length of the array `array` names (PROGRAM-TYPING.md,
 * "Writes at a checked index"). */
interface BoundClaim {
  array: string;
  index: string;
  /** The index is below the length, not only at most it. */
  strict: boolean;
}

/** A term of a proposed linear fact: what the binding `name` holds, the named
 * data fields `path` read from it in turn, read as `term` says
 * (`HeapKnowledge.Term.Kind`): the safe integer it is (`value`), the length of
 * its array store (`length`), or the element count of its typed array
 * (`view`); with an integer coefficient. */
interface LinearTermClaim {
  name: string;
  path: string[];
  term: "value" | "length" | "view";
  coefficient: number;
}

/** A guard of a proposed fact (PROGRAM-TYPING.md, "Guarded clauses"): the
 * named data fields `path` read from what the binding `name` holds give the
 * value `tag` names, or the fact holds. */
interface GuardClaim {
  name: string;
  path: string[];
  tag: "null" | "undefined";
}

/** A linear fact proposed at a statement entry: where none of its guards,
 * in order, reads its tag's value, the sum of the terms is at most `bound`
 * (PROGRAM-TYPING.md, "Linear facts"). */
interface LinearClaim {
  guards: GuardClaim[];
  terms: LinearTermClaim[];
  bound: number;
}

/** A term a quantified fact names: what the binding `name` holds, its named
 * data fields `path` read from it in turn, read as `term` says. */
interface TermRefClaim {
  name: string;
  path: string[];
  term: "value" | "length" | "view";
}

/** A variable of a quantified fact's body: the index, the element at it, or a term. */
type BodyVariableClaim = "index" | "elem" | { term: { ref: TermRefClaim } };

/** A quantified fact proposed at a statement entry (PROGRAM-TYPING.md,
 * "Quantified clauses"): for every index below `stop` of the array the path
 * `path` reads from the binding `name`, each body fact `Σ c·x ≤ bound`. */
interface QuantifiedClaim {
  name: string;
  path: string[];
  stop: TermRefClaim;
  body: { terms: [BodyVariableClaim, number][]; bound: number }[];
}

/** The environment at one shared control-flow point, with source provenance. */
interface EntryClaim<L = Label> {
  point: string;
  start: number;
  bindings: NamedPoint<L>[];
  bounds: BoundClaim[];
  facts: LinearClaim[];
  quantified: QuantifiedClaim[];
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
  /** The producer's rows: the four primitives, then its own rows, each a
   * union of clauses or a scheme (a generic method's or class's callable). */
  types: (Row<L> | SchemeRow<L>)[];
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

/** The claims document a parsed value states, decoded field by field against
 * the types above: every field present, no other field, every label a row of
 * its own document's table or a label tree, as fresh objects. Lean's decoder
 * reads the same document and checks what these types do not state (label
 * order, binder scopes, spans against the source). */
export function decodeSourceClaims(value: Json): SourceClaims {
  requireWellFormed(value, "claims document");
  return claimsDocument(value);
}
function fail(what: string): never {
  throw Error(`claims document: ${what}`);
}
/** An object of exactly the `required` and the present `optional` keys. */
function record(v: JsonRead, what: string, required: readonly string[], optional: readonly string[] = []): JsonObject {
  if (!isJsonObject(v) || !hasExactly(v, required, optional)) fail(`${what}: expected exactly the fields ${required.join(", ")}`);
  return v;
}
function list(v: JsonRead, what: string): readonly JsonValue[] {
  if (!isJsonList(v)) fail(`${what}: expected a list`);
  return v;
}
function each<T>(v: JsonRead, what: string, decode: (x: JsonValue) => T): T[] {
  const result: T[] = [];
  for (const x of list(v, what)) result.push(decode(x));
  return result;
}
function text(v: JsonRead, what: string): string {
  if (typeof v !== "string") fail(`${what}: expected a string`);
  return v;
}
function name(v: JsonRead, what: string): string {
  const s = text(v, what);
  if (s === "") fail(`${what}: expected a nonempty string`);
  return s;
}
function flag(v: JsonRead, what: string): boolean {
  if (typeof v !== "boolean") fail(`${what}: expected a Boolean`);
  return v;
}
function index(v: JsonRead, what: string): number {
  if (typeof v !== "number" || !Number.isSafeInteger(v) || v < 0) fail(`${what}: expected a non-negative integer`);
  return v;
}
function span(v: JsonRead, what: string): Span {
  const pair = list(v, what);
  if (pair.length !== 2) fail(`${what}: expected a [start, end] span`);
  return [index(pair[0], what), index(pair[1], what)];
}
function propertyKey(v: JsonRead, what: string): PropertyKey {
  if (typeof v === "string") return v;
  return { symbol: index(record(v, what, ["symbol"]).symbol, what) };
}
function claimsDocument(v: JsonRead): SourceClaims {
  const o = record(v, "the document", ["file", "sourceSha256", "types", "functions", "modules", "qualified"], ["init"]);
  const rows = list(o.types, "types");
  const label = (x: JsonRead): Label => {
    if (typeof x === "number") {
      if (!Number.isSafeInteger(x) || x < 0 || x >= rows.length) fail("a label names no row of the document's types");
      return x;
    }
    if (isJsonObject(x) && "decl" in x) {
      const r = record(x, "a declaration's label", ["decl"], ["args"]);
      const decl = index(r.decl, "a declaration's label");
      if (!("args" in r)) return { decl };
      const args = each(r.args, "a declaration's arguments", labels);
      if (args.length === 0) fail("a nullary declaration's label leaves its arguments out");
      return { decl, args };
    }
    if (isJsonObject(x) && "meet" in x) {
      const parts = each(record(x, "a meet", ["meet"]).meet, "a meet", labels);
      if (parts.length < 2) fail("a meet has at least two parts");
      return { meet: parts };
    }
    if (isJsonObject(x) && "array" in x) {
      const r = record(x, "an array's label", ["array", "readonly"]);
      return { array: labels(r.array), readonly: flag(r.readonly, "an array's readonly flag") };
    }
    return { binder: name(record(x, "a label", ["binder"]).binder, "a binder's label") };
  };
  const labels = (x: JsonRead): Label[] => each(x, "a label list", label);
  const claimType = (x: JsonRead): ClaimType => {
    if (isJsonList(x)) return labels(x);
    const r = record(x, "a claim type", [], ["param", "array", "union", "scheme", "unavailable"]);
    const keys = Object.keys(r);
    if (keys.length !== 1) fail("a claim type has exactly one field");
    if ("param" in r) return { param: name(r.param, "a rigid parameter") };
    if ("array" in r) return { array: claimType(r.array) };
    if ("union" in r) return { union: each(r.union, "a union", claimType) };
    if ("unavailable" in r) return { unavailable: name(r.unavailable, "an unavailable claim's reason") };
    const s = record(r.scheme, "a scheme", ["effect", "typeParams", "this", "params", "rest", "result"]);
    const effect = decodeCallEffect(s.effect);
    if (effect === undefined) fail("a scheme's effect");
    return {
      scheme: {
        effect,
        typeParams: each(s.typeParams, "a scheme's type parameters", typeParameter),
        this: claimType(s.this),
        params: each(s.params, "a scheme's parameters", claimType),
        rest: s.rest === null ? null : claimType(s.rest),
        result: claimType(s.result),
      },
    };
  };
  const typeParameter = (x: JsonRead): SourceTypeParameter<ClaimType> => {
    const r = record(x, "a type parameter", ["name", "bound", "resolution"]);
    const bound = r.bound === null ? null : claimType(r.bound);
    let resolution: ResolutionSlots | null = null;
    if (r.resolution !== null) {
      const slots = record(r.resolution, "a type parameter's resolution", ["observation", "result"]);
      resolution = { observation: name(slots.observation, "an observation slot"),
        result: slots.result === null ? null : name(slots.result, "a result slot") };
    }
    return { name: name(r.name, "a type parameter's name"), bound, resolution };
  };
  const current = (x: JsonRead): CurrentFields | null =>
    x === null ? null : each(x, "a point's current fields", (pair) => {
      const p = list(pair, "a current field");
      if (p.length !== 2) fail("a current field is a path and its labels");
      const path = each(p[0], "a current field's path", (k) => propertyKey(k, "a path's key"));
      if (path.length === 0) fail("a current field's path is nonempty");
      const field: [PropertyKey[], Label[]] = [path, labels(p[1])];
      return field;
    });
  const namedPoint = (x: JsonRead): NamedPoint => {
    const r = record(x, "a named point", ["name", "type", "current"]);
    return { name: name(r.name, "a point's name"), type: claimType(r.type), current: current(r.current) };
  };
  const entry = (x: JsonRead): EntryClaim => {
    const r = record(x, "an entry", ["point", "start", "bindings", "bounds", "facts", "quantified"]);
    const integer = (v: JsonRead, what: string): number => {
      if (typeof v !== "number" || !Number.isSafeInteger(v)) fail(`${what} is a safe integer`);
      return v;
    };
    const termRef = (t: JsonRead): TermRefClaim => {
      const q = record(t, "a term", ["name", "path", "term"]);
      const kind = q.term;
      if (kind !== "value" && kind !== "length" && kind !== "view") fail("a term's kind is value, length or view");
      return { name: name(q.name, "a term's name"), path: each(q.path, "a term's path", (f) => name(f, "a path's field")),
        term: kind };
    };
    return { point: text(r.point, "an entry's point"), start: index(r.start, "an entry's start"),
      bindings: each(r.bindings, "an entry's bindings", namedPoint),
      bounds: each(r.bounds, "an entry's bounds", (b) => {
        const q = record(b, "a bound", ["array", "index", "strict"]);
        if (typeof q.strict !== "boolean") fail("a bound's strict is a Boolean");
        return { array: name(q.array, "a bound's array"), index: name(q.index, "a bound's index"),
          strict: q.strict };
      }),
      facts: each(r.facts, "an entry's facts", (f) => {
        const q = record(f, "a linear fact", ["guards", "terms", "bound"]);
        const integer = (v: JsonRead, what: string): number => {
          if (typeof v !== "number" || !Number.isSafeInteger(v)) fail(`${what} is a safe integer`);
          return v;
        };
        return {
          guards: each(q.guards, "a fact's guards", (g) => {
            const r = record(g, "a fact's guard", ["name", "path", "tag"]);
            if (r.tag !== "null" && r.tag !== "undefined") fail("a guard's tag is null or undefined");
            const guard: GuardClaim = { name: name(r.name, "a guard's name"),
              path: each(r.path, "a guard's path", (f) => name(f, "a path's field")), tag: r.tag };
            return guard;
          }),
          terms: each(q.terms, "a fact's terms", (t) => {
            const r = record(t, "a fact's term", ["name", "path", "term", "coefficient"]);
            const kind = r.term;
            if (kind !== "value" && kind !== "length" && kind !== "view") fail("a term's kind is value, length or view");
            const term: LinearTermClaim = { name: name(r.name, "a term's name"),
              path: each(r.path, "a term's path", (f) => name(f, "a path's field")), term: kind,
              coefficient: integer(r.coefficient, "a term's coefficient") };
            return term;
          }),
          bound: integer(q.bound, "a fact's bound"),
        };
      }),
      quantified: each(r.quantified, "an entry's quantified facts", (f) => {
        const q = record(f, "a quantified fact", ["name", "path", "stop", "body"]);
        return { name: name(q.name, "a quantified fact's array"),
          path: each(q.path, "a quantified fact's path", (g) => name(g, "a path's field")), stop: termRef(q.stop),
          body: each(q.body, "a quantified fact's body", (b) => {
            const r = record(b, "a body fact", ["terms", "bound"]);
            return { terms: each(r.terms, "a body fact's terms", (t): [BodyVariableClaim, number] => {
              if (!isJsonList(t) || t.length !== 2) fail("a body term is a variable and a coefficient");
              const v = t[0];
              const variable: BodyVariableClaim = v === "index" || v === "elem" ? v
                : { term: { ref: termRef(record(record(v, "a body variable", ["term"]).term, "a body term", ["ref"]).ref) } };
              return [variable, integer(t[1], "a body term's coefficient")];
            }), bound: integer(r.bound, "a body fact's bound") };
          }) };
      }) };
  };
  const certificate = (x: JsonRead): ResolutionCertificate => {
    const k = isJsonObject(x) ? x.k : undefined;
    if (k === "stable") {
      record(x, "a stable certificate", ["k"]);
      return { k: "stable" };
    }
    if (k === "promise") {
      record(x, "a promise certificate", ["k"]);
      return { k: "promise" };
    }
    if (k === "native") return { k: "native", child: certificate(record(x, "a native certificate", ["k", "child"]).child) };
    if (k === "union")
      return { k: "union", arms: each(record(x, "a union certificate", ["k", "arms"]).arms, "a union's arms", certificate) };
    if (k === "binder")
      return { k: "binder", binder: name(record(x, "a binder certificate", ["k", "binder"]).binder, "a certificate's binder") };
    return fail("an unknown resolution certificate");
  };
  const typeArgument = (x: JsonRead): TypeArgument => {
    const r = record(x, "a type argument", ["name", "type", "resolution"]);
    const resolution = r.resolution === null ? null
      : { certificate: certificate(record(r.resolution, "a type argument's resolution", ["certificate"]).certificate) };
    return { name: name(r.name, "a type argument's binder"), type: claimType(r.type), resolution };
  };
  const expression = (x: JsonRead): ExpressionClaim => {
    const r = record(x, "an expression claim", ["point", "pos", "type", "current"], ["instantiate"]);
    const claim: ExpressionClaim = { point: text(r.point, "an expression's point"), pos: span(r.pos, "an expression's span"),
      type: claimType(r.type), current: current(r.current) };
    if ("instantiate" in r)
      claim.instantiate = r.instantiate === null ? null : each(r.instantiate, "an instantiation", typeArgument);
    return claim;
  };
  const contract = (x: JsonRead): StorageContract => {
    const r = record(x, "a storage contract", ["pos", "name", "type"]);
    return { pos: span(r.pos, "a contract's span"), name: name(r.name, "a contract's name"), type: claimType(r.type) };
  };
  const body = (r: JsonObject): BodyClaims => {
    const claims: BodyClaims = {
      contracts: each(r.contracts, "contracts", contract),
      entries: each(r.entries, "entries", entry),
      expressions: each(r.expressions, "expressions", expression),
    };
    if ("arrows" in r)
      claims.arrows = each(r.arrows, "arrows", (a) => {
        const arrow = record(a, "an arrow's claims", ["pos", "rows"]);
        return { pos: span(arrow.pos, "an arrow's span"), rows: each(arrow.rows, "an arrow's rows", (row) => {
          const rr = record(row, "an arrow row", ["contracts", "expressions", "entries"]);
          return { contracts: each(rr.contracts, "contracts", contract),
            expressions: each(rr.expressions, "expressions", expression), entries: each(rr.entries, "entries", entry) };
        }) };
      });
    return claims;
  };
  const fn = (x: JsonRead): FunctionClaims => {
    const r = record(x, "a function's claims",
      ["name", "namePos", "params", "result", "contracts", "footprint", "onThrow", "entries", "expressions"], ["arrows"]);
    const footprint = decodeClosedFootprint(r.footprint);
    if (footprint === undefined) fail("a function's footprint");
    const { contracts, entries, expressions, arrows } = body(r);
    const claims: FunctionClaims = { name: name(r.name, "a function's name"), namePos: span(r.namePos, "a function's name span"),
      params: each(r.params, "a function's parameters", namedPoint), result: claimType(r.result),
      footprint, onThrow: flag(r.onThrow, "a function's onThrow flag"), contracts, entries, expressions };
    if (arrows !== undefined) claims.arrows = arrows;
    return claims;
  };
  const identity = (x: JsonRead): DeclarationIdentity => {
    const r = record(x, "a qualified read", ["module", "name", "span"]);
    return { module: text(r.module, "a qualified read's module"), name: name(r.name, "a qualified read's name"),
      span: span(r.span, "a qualified read's span") };
  };
  const document: SourceClaims = {
    file: text(o.file, "file"),
    sourceSha256: text(o.sourceSha256, "sourceSha256"),
    types: decodeRows(rows, label),
    functions: each(o.functions, "functions", fn),
    modules: each(o.modules, "modules", claimsDocument),
    qualified: each(o.qualified, "qualified", identity),
  };
  if ("init" in o) document.init = body(record(o.init, "init", ["contracts", "entries", "expressions"], ["arrows"]));
  return document;
}
