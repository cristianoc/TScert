import { isArrayPresence, type ArrayPresence } from "./type-graph.mts";
/** Structural claim language at the producer/report boundary, mirroring
 * Claim.lean. Source annotations are type terms (declaration-types.mts); Lean
 * converts them to these types for its source readers. Runtime data is decoded
 * before it is printed as text; unsupported producer shapes are shown as
 * their raw JSON. Its surface text is in claim-text.mts.
 */
import type { PropertyKey } from "./declaration-types.mts";
import type { JsonObject, JsonRead, JsonValue } from "./calculus.mts";
type ClaimType = {
  top: boolean;
  atoms: Atom[];
};
type Field = {
  /** A string key, or `{ symbol: i }`: the declaration document's i-th symbol. */
  name: PropertyKey;
  optional: boolean;
  read: ClaimType;
  write: ClaimType;
};
type RecordAtom = {
  a: "record";
  fields: Field[];
  indexes: { string: string; number: string; symbol: string };
  /** A real string index contract, distinct from the producer's synthetic
   * index markers above. A readonly signature has a never write type. */
  indexSignature?: { read: ClaimType; write: ClaimType };
  call: string;
  construct: string;
  array: string;
  and?: Atom[];
};
type FunctionAtom = {
  a: "function";
  /* The receiver a call may pass: `unknown` for a signature indifferent to
     it, the declared `this` type otherwise. Every signature states it. */
  this: ClaimType;
  params: ClaimType[];
  /* The contract of each actual after `params`, when the signature takes any
     number of them: `(...rest: T[]) => R` has no params and rest `T`. */
  rest?: ClaimType;
  result: ClaimType;
  construct: string;
  array: string;
  and?: Atom[];
};
export type Atom =
  | { a: "null" | "undefined" | "boolean" | "string" | "number" | "bigint" | "symbol" }
  /* A construct signature, `new (params) => result`: what a class meets. */
  | { a: "constructor"; params: ClaimType[]; result: ClaimType }
  /* A `void` result: no usable guarantee about the value. */
  | { a: "void" }
  /* An array: a tuple contract on its store. `required` positions are
     present; `optional` ones may be holes; `rest` types any further position,
     or null when none may exist. `readonly` makes it a view. */
  | {
      a: "array" | "store";
      required: ClaimType[];
      optional: ClaimType[];
      rest: ClaimType | null;
      readonly: boolean;
      presence: ArrayPresence;
    }
  | { a: "stringlit" | "numberlit" | "booleanlit"; v: string }
  /* One bigint, `v` its canonical decimal integer: `-5`, never `-05`. */
  | { a: "bigintlit"; v: string }
  | { a: "param"; name: string }
  | { a: "alias"; name: string; args: ClaimType[] }
  | RecordAtom
  | FunctionAtom
  | { a: "callable"; function: FunctionAtom; bag: RecordAtom };

const isRecord = (v: JsonRead): v is JsonObject =>
  typeof v === "object" && v !== null && !Array.isArray(v);
function object(v: JsonRead): JsonObject {
  if (!isRecord(v)) throw Error("expected an object");
  return v;
}
function keys(
  v: JsonObject,
  required: string[],
  optional: string[] = [],
): void {
  if (
    required.some((k) => !(k in v)) ||
    Object.keys(v).some((k) => ![...required, ...optional].includes(k))
  )
    throw Error("unexpected or missing claim field");
}
const isList = (v: JsonRead): v is readonly JsonValue[] => Array.isArray(v);
function list(v: JsonRead): readonly JsonValue[] {
  if (!isList(v)) throw Error("expected a list");
  return v;
}
/** Checks and narrows, so a caller that goes on to read the string needs no
 * second word for it. */
function str(v: JsonRead): asserts v is string {
  if (typeof v !== "string") throw Error("expected a string");
}
function bool(v: JsonRead): void {
  if (typeof v !== "boolean") throw Error("expected a boolean");
}
function atom(v: JsonRead): void {
  const o = object(v);
  switch (o.a) {
    case "null":
    case "undefined":
    case "boolean":
    case "string":
    case "number":
    case "bigint":
    case "symbol":
    case "void":
      keys(o, ["a"]);
      break;
    case "array":
    case "store":
      keys(o, ["a", "required", "optional", "rest", "readonly", "presence"]);
      for (const t of list(o.required)) decodeClaimType(t);
      for (const t of list(o.optional)) decodeClaimType(t);
      if (o.rest !== null) decodeClaimType(o.rest);
      if (!isArrayPresence(o.presence)) throw Error("invalid density flag");
      if (typeof o.readonly !== "boolean") throw Error("invalid readonly flag");
      break;
    case "booleanlit":
    case "numberlit":
    case "stringlit":
    case "bigintlit":
      keys(o, ["a", "v"]);
      str(o.v);
      if (o.a === "bigintlit" && !/^(0|-?[1-9][0-9]*)$/.test(o.v))
        throw Error("invalid bigint literal");
      if (o.a === "booleanlit" && o.v !== "true" && o.v !== "false")
        throw Error("invalid boolean literal");
      if (o.a === "numberlit" && !Number.isFinite(Number(o.v)))
        throw Error("invalid number literal");
      break;
    case "record": {
      keys(
        o,
        ["a", "fields", "indexes", "call", "construct", "array"],
        ["and", "indexSignature"],
      );
      const names = new Set();
      for (const f of list(o.fields)) {
        const field = object(f);
        keys(field, ["name", "optional", "read", "write"]);
        str(field.name);
        bool(field.optional);
        decodeClaimType(field.read);
        decodeClaimType(field.write);
        if (names.has(field.name)) throw Error("duplicate field");
        names.add(field.name);
      }
      const indexes = object(o.indexes);
      keys(indexes, ["string", "number", "symbol"]);
      Object.values(indexes).forEach(str);
      if (o.indexSignature !== undefined) {
        const index = object(o.indexSignature);
        keys(index, ["read", "write"]);
        decodeClaimType(index.read);
        decodeClaimType(index.write);
      }
      str(o.call);
      str(o.construct);
      str(o.array);
      if (o.and !== undefined) list(o.and).forEach(atom);
      break;
    }
    case "function":
      keys(
        o,
        ["a", "this", "params", "result", "construct", "array"],
        ["and", "rest"],
      );
      decodeClaimType(o.this);
      list(o.params).forEach(decodeClaimType);
      if (o.rest !== undefined) decodeClaimType(o.rest);
      decodeClaimType(o.result);
      str(o.construct);
      str(o.array);
      if (o.and !== undefined) list(o.and).forEach(atom);
      break;
    case "callable":
      keys(o, ["a", "function", "bag"]);
      atom(o.function);
      atom(o.bag);
      if (object(o.function).a !== "function" || object(o.bag).a !== "record")
        throw Error("invalid callable");
      break;
    case "param":
      keys(o, ["a", "name"]);
      str(o.name);
      if (!o.name.length) throw Error("empty type-parameter name");
      break;
    case "alias":
      keys(o, ["a", "name", "args"]);
      str(o.name);
      if (!o.name.length) throw Error("empty alias name");
      list(o.args).forEach(decodeClaimType);
      break;
    default:
      throw Error("unknown claim atom");
  }
}
export function decodeClaimType(v: JsonValue): ClaimType {
  const o = object(v);
  keys(o, ["top", "atoms"]);
  bool(o.top);
  list(o.atoms).forEach(atom);
  if (o.top && list(o.atoms).length)
    throw Error("unknown cannot also carry atoms");
  // asserted: the decoder's result, checked field by field above
  return o as ClaimType;
}
