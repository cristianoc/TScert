import { isArrayPresence, type ArrayPresence } from "./type-graph.mts";
/** Structural claim language at the producer/report boundary, mirroring
 * Claim.lean. Source annotations are type terms (declaration-types.mts); Lean
 * converts them to these types for its source readers. Runtime data is decoded
 * before it is printed as text; unsupported producer shapes are shown as
 * their raw JSON. Its surface text is in claim-text.mts.
 */
import type { PropertyKey } from "./declaration-types.mts";
import {
  hasExactly,
  isJsonList,
  isJsonObject,
  type JsonObject,
  type JsonRead,
  type JsonValue,
} from "./calculus.mts";
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

function object(v: JsonRead): JsonObject {
  if (!isJsonObject(v)) throw Error("expected an object");
  return v;
}
function keys(
  v: JsonObject,
  required: string[],
  optional: string[] = [],
): void {
  if (!hasExactly(v, required, optional))
    throw Error("unexpected or missing claim field");
}
function list(v: JsonRead): readonly JsonValue[] {
  if (!isJsonList(v)) throw Error("expected a list");
  return v;
}
/** Checks and narrows, so a caller that goes on to read the string needs no
 * second word for it. */
function str(v: JsonRead): asserts v is string {
  if (typeof v !== "string") throw Error("expected a string");
}
function bool(v: JsonRead): asserts v is boolean {
  if (typeof v !== "boolean") throw Error("expected a boolean");
}
/** A list of claim types, each decoded as the list is read. */
function claimTypes(v: JsonRead): ClaimType[] {
  const result: ClaimType[] = [];
  for (const t of list(v)) result.push(decodeClaimType(t));
  return result;
}
/** The atoms a list holds, each decoded as the list is read. */
function atoms(v: JsonRead): Atom[] {
  const result: Atom[] = [];
  for (const a of list(v)) result.push(atom(a));
  return result;
}
/** A record atom's fields, each name once. */
function recordFields(v: JsonRead): Field[] {
  const names = new Set<string>();
  const fields: Field[] = [];
  for (const f of list(v)) {
    const field = object(f);
    keys(field, ["name", "optional", "read", "write"]);
    const name = field.name;
    str(name);
    const optional = field.optional;
    bool(optional);
    const read = decodeClaimType(field.read);
    const write = decodeClaimType(field.write);
    if (names.has(name)) throw Error("duplicate field");
    names.add(name);
    fields.push({ name, optional, read, write });
  }
  return fields;
}
/** A record atom's synthetic index markers. */
function indexMarkers(v: JsonRead): RecordAtom["indexes"] {
  const indexes = object(v);
  keys(indexes, ["string", "number", "symbol"]);
  const string = indexes.string;
  const number = indexes.number;
  const symbol = indexes.symbol;
  str(string);
  str(number);
  str(symbol);
  return { string, number, symbol };
}
function recordAtom(v: JsonObject): RecordAtom {
  keys(
    v,
    ["a", "fields", "indexes", "call", "construct", "array"],
    ["and", "indexSignature"],
  );
  const fields = recordFields(v.fields);
  const indexes = indexMarkers(v.indexes);
  let indexSignature: { read: ClaimType; write: ClaimType } | undefined;
  if (v.indexSignature !== undefined) {
    const index = object(v.indexSignature);
    keys(index, ["read", "write"]);
    const read = decodeClaimType(index.read);
    const write = decodeClaimType(index.write);
    indexSignature = { read, write };
  }
  const call = v.call;
  const construct = v.construct;
  const array = v.array;
  str(call);
  str(construct);
  str(array);
  const and = v.and !== undefined ? atoms(v.and) : undefined;
  return {
    a: "record",
    fields,
    indexes,
    call,
    construct,
    array,
    ...(indexSignature === undefined ? {} : { indexSignature }),
    ...(and === undefined ? {} : { and }),
  };
}
function functionAtom(v: JsonObject): FunctionAtom {
  keys(
    v,
    ["a", "this", "params", "result", "construct", "array"],
    ["and", "rest"],
  );
  const self = decodeClaimType(v.this);
  const params = claimTypes(v.params);
  const rest = v.rest !== undefined ? decodeClaimType(v.rest) : undefined;
  const result = decodeClaimType(v.result);
  const construct = v.construct;
  const array = v.array;
  str(construct);
  str(array);
  const and = v.and !== undefined ? atoms(v.and) : undefined;
  return {
    a: "function",
    this: self,
    params,
    ...(rest === undefined ? {} : { rest }),
    result,
    construct,
    array,
    ...(and === undefined ? {} : { and }),
  };
}
/** The atom kinds, each once: a kind of `Atom` missing here, or one no atom
 * has, does not compile. */
const ATOM_KINDS = [
  "null", "undefined", "boolean", "string", "number", "bigint", "symbol", "void",
  "constructor", "array", "store", "stringlit", "numberlit", "booleanlit", "bigintlit",
  "param", "alias", "record", "function", "callable",
] as const;
type Covers<Missing extends never> = Missing;
type EveryAtomKind = Covers<Exclude<Atom["a"], (typeof ATOM_KINDS)[number]>>;
type OnlyAtomKinds = Covers<Exclude<(typeof ATOM_KINDS)[number], Atom["a"]>>;
/** A literal atom's text. */
function literalText(v: JsonObject): string {
  keys(v, ["a", "v"]);
  const value = v.v;
  str(value);
  return value;
}
/** The atom a value states, as fresh objects of its fields. */
function atom(v: JsonRead): Atom {
  const o = object(v);
  const a = ATOM_KINDS.find((k) => k === o.a);
  switch (a) {
    case "null":
    case "undefined":
    case "boolean":
    case "string":
    case "number":
    case "bigint":
    case "symbol":
      keys(o, ["a"]);
      return { a };
    case "void":
      keys(o, ["a"]);
      return { a };
    case "array":
    case "store": {
      keys(o, ["a", "required", "optional", "rest", "readonly", "presence"]);
      const required = claimTypes(o.required);
      const optional = claimTypes(o.optional);
      const rest = o.rest !== null ? decodeClaimType(o.rest) : null;
      const presence = o.presence;
      if (!isArrayPresence(presence)) throw Error("invalid density flag");
      const readonly = o.readonly;
      if (typeof readonly !== "boolean") throw Error("invalid readonly flag");
      return { a, required, optional, rest, readonly, presence };
    }
    case "booleanlit":
    case "numberlit":
    case "stringlit": {
      const value = literalText(o);
      if (a === "booleanlit" && value !== "true" && value !== "false")
        throw Error("invalid boolean literal");
      if (a === "numberlit" && !Number.isFinite(Number(value)))
        throw Error("invalid number literal");
      return { a, v: value };
    }
    case "bigintlit": {
      const value = literalText(o);
      if (!/^(0|-?[1-9][0-9]*)$/.test(value))
        throw Error("invalid bigint literal");
      return { a, v: value };
    }
    case "record":
      return recordAtom(o);
    case "function":
      return functionAtom(o);
    case "callable": {
      keys(o, ["a", "function", "bag"]);
      const fn = object(o.function);
      const bag = object(o.bag);
      if (fn.a !== "function" || bag.a !== "record") {
        atom(fn);
        atom(bag);
        throw Error("invalid callable");
      }
      return { a, function: functionAtom(fn), bag: recordAtom(bag) };
    }
    case "param": {
      keys(o, ["a", "name"]);
      const name = o.name;
      str(name);
      if (!name.length) throw Error("empty type-parameter name");
      return { a, name };
    }
    case "alias": {
      keys(o, ["a", "name", "args"]);
      const name = o.name;
      str(name);
      if (!name.length) throw Error("empty alias name");
      return { a, name, args: claimTypes(o.args) };
    }
    default:
      throw Error("unknown claim atom");
  }
}
/** The claim type a value states, as fresh objects of its fields. */
export function decodeClaimType(v: JsonRead): ClaimType {
  const o = object(v);
  keys(o, ["top", "atoms"]);
  const top = o.top;
  bool(top);
  const decoded = atoms(o.atoms);
  if (top && decoded.length)
    throw Error("unknown cannot also carry atoms");
  return { top, atoms: decoded };
}
