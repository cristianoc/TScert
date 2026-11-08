/* Surface text for the claim language declared in claim.mts, printed here so
 * reports and diagnostics share one syntax. @ followed by a JSON object states
 * nondefault object modes and conjunction metadata explicitly. The text always
 * determines its type. */
import { decodeClaimType, type Atom } from "./claim.mts";
import {
  isJsonList,
  isJsonObject,
  stringOfJson,
  type JsonObject,
  type JsonRead,
  type JsonValue,
} from "./calculus.mts";
import { passToolFailure } from "./thrown.mts";
import {
  numberOfBits,
  isArrayPresence,
  decodeCallEffect,
  ordinaryEffect,
  presencePrefix,
  type ClauseKey,
  type StringClause,
} from "./type-graph.mts";

/* What reaches the printers is the producer's, not this file's: a report shows
 * a claim that did not decode, and the lifter below names parts of a graph the
 * surface has no syntax for. Each is a value of `JsonValue`'s shape, so a read
 * here narrows what arrived rather than assuming a claim. */

/** What a value holds: an object's values, an array's elements, a string's
 * characters; a primitive holds nothing. */
const members = (v: JsonValue): readonly JsonValue[] =>
  isJsonObject(v)
    ? Object.values(v)
    : isJsonList(v)
      ? v
      : typeof v === "string"
        ? [...v]
        : [];
/** An ordinary arrow's effect, the one a structural function atom states. */
/** Each field is compared with `ordinaryEffect`'s, whose promise and kind
 * lists are `null`, so `===` is `sameEffect`'s comparison of them, and whose
 * index-fact lists are empty. */
const isOrdinary = (effect: JsonRead): boolean => {
  const d = decodeCallEffect(effect);
  const o = ordinaryEffect;
  return (
    d !== undefined &&
    d.footprint.value === o.footprint.value &&
    d.footprint.store === o.footprint.store &&
    d.promise === o.promise &&
    d.fresh === o.fresh &&
    d.receiverStore === o.receiverStore &&
    d.onThrow === o.onThrow &&
    d.receiverOwn === o.receiverOwn &&
    d.freshObject === o.freshObject &&
    d.requires === o.requires &&
    d.elements === o.elements &&
    d.pre.length === 0 &&
    d.ensures.length === 0 &&
    d.receiverGrows === o.receiverGrows &&
    d.elementWrite === o.elementWrite
  );
};
/** The atoms whose kind is all there is to them, read off `Atom` rather than
 * restated: the members whose only field is `a`. */
type BareKind<A> = A extends { a: infer K }
  ? keyof A extends "a"
    ? K
    : never
  : never;
const PRIMITIVE: BareKind<Atom>[] = [
  "null",
  "boolean",
  "string",
  "number",
  "bigint",
  "symbol",
  "undefined",
  "void",
];
/** The primitive kind `v` names, found in the table; undefined where it
 * names none. */
const primitiveKind = (v: JsonRead): BareKind<Atom> | undefined =>
  PRIMITIVE.find((p) => p === v);

/* ---------- printing ---------- */
/** Printing never fails; it records whether the text says the whole type. */
interface PrintState {
  printable: boolean;
}

/** The keys of an atom's metadata, literals naming no member of
 * `Object.prototype`. */
type MetadataKey = "call" | "construct" | "array";
function atomText(atom: JsonRead, state: PrintState): Within<{ value: "any"; store: "grow" }, string> {
  const text = bareAtomText(atom, state);
  if (!isJsonObject(atom)) return text;
  // The metadata's entries are collected, each key once, and the object is
  // built from them.
  const entries: [string, JsonValue][] = [];
  const keys: readonly MetadataKey[] = ["call", "construct", "array"];
  for (const key of keys) {
    const value = atom[key];
    if (value !== undefined && value !== "unknown") entries.push([key, value]);
  }
  // Index markers other than all absent are shown, malformed ones too.
  const indexes = atom.indexes;
  if (indexes !== undefined && members(indexes).some((v) => v !== "absent"))
    entries.push(["indexes", indexes]);
  const and = atom.and;
  if (and !== undefined) entries.push(["and", and]);
  return entries.length
    ? (atom.a === "function" ? "(" + text + ")" : text) +
        " @" +
        JSON.stringify(Object.fromEntries(entries))
    : text;
}
function bareAtomText(
  atom: JsonRead,
  state: PrintState,
): Within<{ value: "any"; store: "grow" }, string> {
  // An array where an atom belongs is no atom of any kind.
  if (isJsonList(atom)) {
    state.printable = false;
    return "«type»";
  }
  if (!isJsonObject(atom)) {
    state.printable = false;
    if (
      typeof atom === "string" ||
      typeof atom === "number" ||
      typeof atom === "boolean" ||
      atom === null
    )
      return String(atom);
    return "«type»";
  }
  if (atom.unsupported === true) {
    state.printable = false;
    return "(unavailable)";
  }
  const primitive = primitiveKind(atom.a);
  if (primitive !== undefined && Object.keys(atom).join() === "a")
    return primitive;
  if (
    (atom.a === "array" || atom.a === "store") &&
    isJsonList(atom.required) &&
    isJsonList(atom.optional)
  ) {
    // Both lists are read before a callback runs: `typeText` writes `state`,
    // and a field read after it is read at its contract.
    const requiredTypes = atom.required;
    const optionalTypes = atom.optional;
    const required = requiredTypes.map((t) => typeText(t, state));
    const optional = optionalTypes.map((t) => typeText(t, state) + "?");
    const rest = atom.rest === null ? null : typeText(atom.rest, state);
    const presence = atom.presence;
    const text =
      (isArrayPresence(presence)
        ? presencePrefix(presence)
        : "(invalid presence) ") +
      (required.length === 0 && optional.length === 0 && rest !== null
        ? `${atom.readonly ? "ReadonlyArray" : "Array"}<${rest}>`
        : `${atom.readonly ? "readonly " : ""}[${[...required, ...optional, ...(rest === null ? [] : [`...Array<${rest}>`])].join(", ")}]`);
    return atom.a === "store" ? `Store<${text}>` : text;
  }
  if (atom.a === "param" && typeof atom.name === "string") return atom.name;
  if (atom.a === "alias" && typeof atom.name === "string" && isJsonList(atom.args))
    return (
      atom.name +
      "<" +
      atom.args.map((t) => typeText(t, state)).join(", ") +
      ">"
    );
  if (
    atom.a === "booleanlit" &&
    typeof atom.v === "string" &&
    ["true", "false"].includes(atom.v)
  )
    return atom.v;
  if (atom.a === "stringlit" && typeof atom.v === "string")
    return JSON.stringify(atom.v);
  if (
    (atom.a === "numberlit" || atom.a === "numlit") &&
    typeof atom.v === "string" &&
    Number.isFinite(Number(atom.v))
  )
    return atom.v;
  if (atom.a === "bigintlit" && typeof atom.v === "string") return atom.v + "n";
  if (atom.a === "record" && isJsonList(atom.fields)) {
    // An index signature that is no object is shown in the atom's encoding.
    if (isJsonList(atom.indexSignature)) return JSON.stringify(atom);
    const index = isJsonObject(atom.indexSignature) ? atom.indexSignature : null;
    const never = (t: JsonRead) =>
      isJsonObject(t) && t.top === false && isJsonList(t.atoms) && t.atoms.length === 0;
    if (index && !never(index.write)) return JSON.stringify(atom);
    return (
      "{ " +
      [
        ...atom.fields.map((field) => {
          // A field the producer sent malformed is shown as it is.
          if (!isJsonObject(field))
            return "(invalid field " + JSON.stringify(field) + ")";
          // A name the surface can write is written, anything else quoted,
          // and a symbol key is shown by its index.
          const key = field.name;
          const name =
            (typeof key === "string"
              ? /^[A-Za-z_$][\w$]*$/.test(key)
                ? key
                : JSON.stringify(key)
              : isJsonObject(key) && typeof key.symbol === "number"
                ? `[symbol ${key.symbol}]`
                : key === undefined
                  ? "undefined"
                  : JSON.stringify(key)) + (field.optional ? "?" : "");
          const read = typeText(field.read, state);
          const write = typeText(field.write, state);
          // A read type that differs from the write type is an assertion about
          // the cell's current contents, distinct from the storage invariant it
          // is written against. SOURCE-CLAIMS.md writes that `invariant =
          // (current)`; the two are not a read/write capability.
          return read === write
            ? name + ": " + read
            : name + ": " + write + " = (" + read + ")";
        }),
        ...(index
          ? [`readonly [key: string]: ${typeText(index.read, state)}`]
          : []),
      ].join(", ") +
      " }"
    );
  }
  if (atom.a === "callable")
    return (
      "(" + atomText(atom.function, state) + ") & " + atomText(atom.bag, state)
    );
  if (atom.a === "constructor" && isJsonList(atom.params))
    return (
      "new (" +
      atom.params
        .map((p, i) => "arg" + i + ": " + typeText(p, state))
        .join(", ") +
      ") => " +
      typeText(atom.result, state)
    );
  if (atom.a === "function" && isJsonList(atom.params)) {
    // The parameters are read before `typeText` writes `state`.
    const params = atom.params;
    return (
      "(" +
      [
        // A receiver-indifferent signature has no `this` to show.
        ...(isJsonObject(atom.this) && atom.this.top === true
          ? []
          : ["this: " + typeText(atom.this, state)]),
        ...params.map((p) => typeText(p, state)),
        ...(atom.rest === undefined
          ? []
          : ["...Array<" + typeText(atom.rest, state) + ">"]),
      ].join(", ") +
      ") => " +
      typeText(atom.result, state)
    );
  }
  state.printable = false;
  return atom.a ? "«" + stringOfJson(atom.a) + "»" : "«type»";
}

function typeText(type: JsonRead, state: PrintState): Within<{ value: "any"; store: "grow" }, string> {
  if (type === undefined || type === null) {
    state.printable = false;
    return "«missing»";
  }
  if (typeof type === "string") return type; // already a display string
  // Anything else is read for its fields, which a nonobject simply has none of.
  const shape: JsonObject = isJsonObject(type) ? type : {};
  if (shape.unsupported === true) {
    state.printable = false;
    return "(unavailable)";
  }
  if (shape.top === true) return "unknown";
  const atoms: readonly JsonValue[] | null = isJsonList(shape.atoms)
    ? shape.atoms
    : null;
  if (!atoms) {
    state.printable = false;
    return "«type»";
  }
  if (!atoms.length) return "never";
  return atoms
    .map((atom) => {
      const text = atomText(atom, state);
      const kind = isJsonObject(atom) ? atom.a : undefined;
      // Arrow results extend through a union, so an arrow that is itself a
      // union alternative needs grouping around the whole signature.
      return atoms.length > 1 && (kind === "function" || kind === "callable")
        ? "(" + text + ")"
        : text;
    })
    .join(" | ");
}

/** A type's text, and whether it is the claim language's. */
interface Printed {
  text: string;
  printable: boolean;
}

/** A type's text alone, for a lifted part, whose completeness the whole
 * report's `printType` states. */
const textOf = (
  type: JsonValue,
): Within<{ value: "any"; store: "grow" }, string> =>
  typeText(type, { printable: true });

function printType(type: JsonValue): Printed {
  const state: PrintState = { printable: true };
  try {
    decodeClaimType(type);
  } catch (error) {
    passToolFailure(error);
    state.printable = false;
  }
  const text = typeText(type, state);
  return { text, printable: state.printable };
}

/** A normalized type the structural encoding cannot state. */
class TypeSyntaxError extends Error {}

/* ---------- the normalized encoding ---------- */
// A normalized claim (SOURCE-CLAIMS.md) indexes a table of type rows. It is
// lifted into the structural encoding above to be printed.

/** A type as a report shows it, which is not a `ClaimType`: lifting stops
 * at a depth cut and names an intersection, or a clause it does not know, as
 * text where an atom belongs. The printers above take that in stride. It is
 * a `JsonValue`: a part the graph lacks is written as `null` or left out. */
type Shown = {
  readonly [key: string]: JsonValue;
  top: boolean;
  atoms: JsonValue[];
};

/** A record field as a report shows it. */
type ShownField = {
  readonly [key: string]: JsonValue;
  name: string;
  optional: boolean;
  read: Shown;
  write: Shown;
};

/** A record atom as a report shows it: its fields, and no index, call,
 * construct or array part. */
type ShownRecord = {
  readonly [key: string]: JsonValue;
  a: "record";
  indexes: {
    readonly [key: string]: JsonValue;
    string: "absent";
    number: "absent";
    symbol: "absent";
  };
  call: "unknown";
  construct: "unknown";
  array: "unknown";
  fields: ShownField[];
};

/** A record contract's fields, as the claim language writes them: each field
 * reads and writes at its own invariant. */
const cell = (
  types: Table,
  contract: JsonRead,
  depth: number,
  views: JsonRead = [],
): Within<{ value: "any"; store: "grow" }, ShownRecord> => {
  const entries: readonly JsonValue[] = isJsonList(contract) ? contract : [];
  // A view field reads at its bound and accepts no write.
  const viewed: readonly JsonValue[] = isJsonList(views) ? views : [];
  const viewField = (
    entry: JsonValue,
  ): Within<{ value: "any"; store: "grow" }, ShownField> => {
    const pair: readonly JsonValue[] = isJsonList(entry) ? entry : [];
    const key = pair[0];
    return {
      name: typeof key === "string" ? key : "",
      optional: false,
      read: liftType(types, pair[1], depth),
      write: { top: false, atoms: [] },
    };
  };
  const contractField = (
    entry: JsonValue,
  ): Within<{ value: "any"; store: "grow" }, ShownField> => {
    const pair: readonly JsonValue[] = isJsonList(entry) ? entry : [];
    const key = pair[0];
    const invariant = pair[1];
    const name = typeof key === "string" ? key : "";
    return {
      name,
      optional: false,
      read: liftType(types, invariant, depth),
      write: liftType(types, invariant, depth),
    };
  };
  const readonly = viewed.map(viewField);
  return {
    a: "record",
    indexes: { string: "absent", number: "absent", symbol: "absent" },
    call: "unknown",
    construct: "unknown",
    array: "unknown",
    fields: [
      ...readonly,
      ...entries.map(contractField),
    ],
  };
};

// An intersection of contracts has no surface form; it is shown as text and
// stays on the JSON path, like anything else the surface cannot name.
const shown = (atoms: readonly JsonValue[]): Within<{ value: "any"; store: "grow" }, string> =>
  atoms
    .map((atom) => textOf({ top: false, atoms: [atom] }))
    .join(" & ");

// Every clause kind this lifter names. The graph arrives untyped, so the
// dispatch below cannot be narrowed; this table is checked instead, and a
// clause added to `Clause` without a case here does not compile.
const _handled = {
  nul: 1,
  bool: 1,
  undef: 1,
  num: 1,
  str: 1,
  top: 1,
  source: 1,
  list: 1,
  boolLit: 1,
  numLit: 1,
  strLit: 1,
  refs: 1,
  dict: 1,
  arrs: 1,
  callable: 1,
  ctors: 1,
  pack: 1,
  bigint: 1,
  symbol: 1,
  bigintLit: 1,
  symbolLit: 1,
  numIn: 1,
  strIn: 1,
} satisfies Record<StringClause | ClauseKey, 1>;
void _handled;

// A table being lifted from: its rows, and the source-like name of each row
// that stands for an application (a diagnostic's `names`). A named label is
// shown by its name, not expanded.
interface Table {
  rows: JsonValue;
  names: Map<number, string>;
  /** The depth a lift starts at: a union below it shows its first
   * `nestedArms` arms, then `…`. */
  top: number;
  /** The lifts made from this table, by depth and labels. */
  lifted: Map<string, Shown>;
}

// A nested union of a family's arms is hundreds of objects, each with fields
// of the same union: shown whole, a three-level lift is gigabytes of text.
const nestedArms = 8;

// A row, where the table has one under that label. Both arrive from the
// document, so neither is trusted to be there.
// A label is a row's index, as a number or as its canonical decimal string.
const rowAt = (types: Table, label: JsonValue): JsonRead => {
  // The rows are read once, so that the list test holds at the index read.
  const rows = types.rows;
  if (!isJsonList(rows)) return undefined;
  if (typeof label === "number") return rows[label];
  if (typeof label === "string" && /^(0|[1-9][0-9]*)$/.test(label))
    return rows[Number(label)];
  return undefined;
};

// A tag set's literal clauses; any other clause, itself.
function setLiterals(clause: JsonValue): JsonValue[] {
  if (isJsonObject(clause) && isJsonObject(clause.numIn) && isJsonList(clause.numIn.bits))
    return clause.numIn.bits.map((bits) => ({ numLit: { bits } }));
  if (isJsonObject(clause) && isJsonObject(clause.strIn) && isJsonList(clause.strIn.values))
    return clause.strIn.values.map((value) => ({ strLit: { value } }));
  return [clause];
}

/** A clause's encoding, which a report shows where the surface has no form
 * for it. A `JsonValue` serializes to a string; `undefined` is TypeScript's
 * result for other values. */
const encoding = (clause: JsonValue): string => JSON.stringify(clause) ?? "";

function liftClause(
  types: Table,
  clause: JsonValue,
  depth: number,
): Within<{ value: "any"; store: "grow" }, JsonValue> {
  if (clause === "nul") return { a: "null" };
  if (clause === "bool") return { a: "boolean" };
  if (clause === "undef") return { a: "undefined" };
  if (clause === "num") return { a: "number" };
  if (clause === "str") return { a: "string" };
  if (clause === "bigint") return { a: "bigint" };
  if (clause === "symbol") return { a: "symbol" };
  if (clause === "top") return "calculus top";
  if (clause === "source") return "unknown";
  // A clause states one kind, under its own key. The table above is what
  // says these are all of them; here the key is only read, at one of the
  // literal keys of `ClauseKey`, so no read finds a member of
  // `Object.prototype`.
  const body = (key: ClauseKey): JsonRead =>
    isJsonObject(clause) ? clause[key] : undefined;
  const boolLit = body("boolLit");
  if (boolLit)
    return {
      a: "booleanlit",
      v: stringOfJson(isJsonObject(boolLit) ? boolLit.value : undefined),
    };
  // The surface names the number, not the bit pattern that identifies it.
  const numLit = body("numLit");
  if (numLit)
    return {
      a: "numberlit",
      v: String(
        numberOfBits(stringOfJson(isJsonObject(numLit) ? numLit.bits : undefined)),
      ),
    };
  const bigintLit = body("bigintLit");
  if (bigintLit)
    return {
      a: "bigintlit",
      v: stringOfJson(isJsonObject(bigintLit) ? bigintLit.value : undefined),
    };
  // A symbol singleton has no claim form; the reader names it.
  const symbolLit = body("symbolLit");
  if (symbolLit)
    return `unique symbol ${stringOfJson(isJsonObject(symbolLit) ? symbolLit.id : undefined)}`;
  // A tag set is the union of its literals, which `liftType` lists as atoms;
  // met elsewhere, it is shown as that union's text.
  if (body("numIn") !== undefined || body("strIn") !== undefined)
    return setLiterals(clause)
      .map((c) => JSON.stringify(liftClause(types, c, depth)))
      .join(" | ");
  const strLit = body("strLit");
  if (strLit)
    return {
      a: "stringlit",
      v: stringOfJson(isJsonObject(strLit) ? strLit.value : undefined),
    };
  // The graph is finite but may be cyclic, so lifting stops rather than recursing.
  if (depth <= 0) return "…";
  const list = body("list");
  if (isJsonObject(list) && isJsonObject(list.first) && isJsonList(list.rest)) {
    const t = list.first;
    // Read before `liftType`, which writes `types.lifted`, runs.
    const required = t.required;
    const optional = t.optional;
    if (list.rest.length || !isJsonList(required) || !isJsonList(optional))
      return encoding(clause);
    return {
      a: "store",
      required: required.map((a) => liftType(types, a, depth - 1)),
      optional: optional.map((a) => liftType(types, a, depth - 1)),
      rest: t.rest === null ? null : liftType(types, t.rest, depth - 1),
      // A flag the graph lacks is left out.
      ...(t.readonly === undefined ? {} : { readonly: t.readonly }),
      ...(t.presence === undefined ? {} : { presence: t.presence }),
    };
  }
  const refs = body("refs");
  if (refs) {
    const first = isJsonObject(refs) ? refs.first : undefined;
    const rest: readonly JsonValue[] =
      isJsonObject(refs) && isJsonList(refs.rest) ? refs.rest : [];
    const views = isJsonObject(refs) ? refs.views : undefined;
    // The first cell, possibly absent, takes the views; the rest, JSON
    // values, are mapped.
    const later = (
      c: JsonValue,
    ): Within<{ value: "any"; store: "grow" }, ShownRecord> =>
      cell(types, c, depth - 1, []);
    const cells = [cell(types, first, depth - 1, views), ...rest.map(later)];
    const [only] = cells;
    if (only === undefined || cells.length !== 1) return shown(cells);
    const [f] = only.fields;
    if (f !== undefined && only.fields.length === 1) {
      const store = f.read.atoms[0];
      if (
        f.name === "[]" &&
        isJsonObject(store) &&
        store.a === "store" &&
        ((same(f.read, f.write) && store.readonly === false) ||
          (f.write.atoms.length === 0 && store.readonly === true))
      )
        return { ...store, a: "array" };
    }
    return only;
  }
  const dict = body("dict");
  if (isJsonObject(dict)) {
    const indexes: readonly JsonValue[] = isJsonList(dict.indexes)
      ? dict.indexes
      : [];
    const index: JsonRead = indexes[0];
    if (
      !isJsonList(dict.rest) ||
      dict.rest.length ||
      !isJsonList(dict.indexes) ||
      indexes.length !== 1 ||
      !isJsonList(index) ||
      index.length !== 2
    )
      return encoding(clause);
    const record = cell(types, dict.first, depth - 1, dict.views);
    // The record's fields are named: a spread of `ShownRecord`, a
    // dictionary, states no keys.
    return {
      a: record.a,
      indexes: record.indexes,
      call: record.call,
      construct: record.construct,
      array: record.array,
      fields: record.fields,
      indexSignature: {
        read: liftType(types, index[1], depth - 1),
        write: { top: false, atoms: [] },
      },
    };
  }
  const callable = body("callable");
  if (callable) {
    const c: JsonObject = isJsonObject(callable) ? callable : {};
    const rest: readonly JsonValue[] = isJsonList(c.rest) ? c.rest : [];
    const fixed: readonly JsonValue[] = isJsonList(c.arrows) ? c.arrows : [];
    const variadic: readonly JsonValue[] = isJsonList(c.variadic) ? c.variadic : [];
    if (
      [...fixed, ...variadic].some((s) => !isJsonObject(s) || !isOrdinary(s.effect))
    )
      return encoding(clause);
    const signatures = liftSignatures(types, c.arrows, c.variadic, depth);
    const [signature] = signatures;
    if (rest.length || signature === undefined || signatures.length !== 1)
      return encoding(clause);
    return {
      a: "callable",
      function: signature,
      bag: cell(types, c.first, depth - 1),
    };
  }
  const arrs = body("arrs");
  if (isJsonObject(arrs)) {
    const fixed: readonly JsonValue[] = isJsonList(arrs.arrows) ? arrs.arrows : [];
    const variadic: readonly JsonValue[] = isJsonList(arrs.variadic)
      ? arrs.variadic
      : [];
    if (
      [...fixed, ...variadic].some((s) => !isJsonObject(s) || !isOrdinary(s.effect))
    )
      return encoding(clause);
    const arrows = liftSignatures(types, arrs.arrows, arrs.variadic, depth);
    const [arrow] = arrows;
    if (arrow !== undefined) return arrows.length === 1 ? arrow : shown(arrows);
  }
  // Unknown clauses are shown as their encoding rather than guessed at.
  return encoding(clause);
}

/** A clause's call signatures as function atoms: its fixed arrows, then its
variadic ones, whose further actuals are at `rest`: an element rest's element,
or the rest type itself when it is no element rest. */
function liftSignatures(
  types: Table,
  fixed: JsonRead,
  variadic: JsonRead,
  depth: number,
): Within<{ value: "any"; store: "grow" }, JsonObject[]> {
  const atom = (
    receiver: JsonRead,
    domain: JsonRead,
    result: JsonRead,
    element?: JsonRead,
  ): Within<{ value: "any"; store: "grow" }, JsonObject> => {
    const domains: readonly JsonValue[] = isJsonList(domain) ? domain : [];
    return {
      a: "function",
      construct: "unknown",
      array: "unknown",
      this: liftType(types, receiver, depth - 1),
      params: domains.map((D) => liftType(types, D, depth - 1)),
      ...(element === undefined
        ? {}
        : { rest: liftType(types, element, depth - 1) }),
      result: liftType(types, result, depth - 1),
    };
  };
  const arrows: readonly JsonValue[] = isJsonList(fixed) ? fixed : [];
  const sigs: readonly JsonValue[] = isJsonList(variadic) ? variadic : [];
  const fixedAtom = (
    arrow: JsonValue,
  ): Within<{ value: "any"; store: "grow" }, JsonObject> => {
    if (!isJsonObject(arrow) || !isOrdinary(arrow.effect))
      throw new TypeSyntaxError("a qualified signature has no structural form");
    return atom(arrow.receiver, arrow.arguments, arrow.result);
  };
  const variadicAtom = (
    sig: JsonValue,
  ): Within<{ value: "any"; store: "grow" }, JsonObject> => {
    if (!isJsonObject(sig) || !isOrdinary(sig.effect))
      throw new TypeSyntaxError("a qualified signature has no structural form");
    const [domain, rest]: readonly JsonRead[] = isJsonList(sig.arguments)
      ? sig.arguments
      : [];
    return atom(sig.receiver, domain, sig.result, restElement(types, rest));
  };
  return [...arrows.map(fixedAtom), ...sigs.map(variadicAtom)];
}

/** The element of an element rest: a type whose one clause is the pack of
any number of actuals at it. Any other rest type is shown as itself. */
function restElement(types: Table, rest: JsonRead): JsonRead {
  if (!isJsonList(rest) || rest.length !== 1) return rest;
  const [label] = rest;
  const row = label === undefined ? undefined : rowAt(types, label);
  const clause: JsonRead = isJsonList(row) && row.length === 1 ? row[0] : undefined;
  const pack = isJsonObject(clause) ? clause.pack : undefined;
  if (!isJsonObject(pack) || !isJsonList(pack.rest) || pack.rest.length) return rest;
  const t = pack.first;
  if (
    !isJsonObject(t) ||
    !isJsonList(t.required) ||
    t.required.length ||
    !isJsonList(t.optional) ||
    t.optional.length ||
    t.readonly !== false ||
    t.rest === null
  )
    return rest;
  return t.rest;
}

// A lift is a function of its labels and depth within one table, so a label
// list lifted once at a depth is reused there.
function liftType(
  types: Table,
  labels: JsonRead,
  depth: number,
): Within<{ value: "any"; store: "grow" }, Shown> {
  // An absent list is keyed as the text an interpolation of the absent
  // serialization gives.
  const at = `${depth}:${labels === undefined ? "undefined" : JSON.stringify(labels)}`;
  const held = types.lifted.get(at);
  if (held !== undefined) return held;
  const lifted = liftLabels(types, labels, depth);
  types.lifted.set(at, lifted);
  return lifted;
}

function liftLabels(
  types: Table,
  labels: JsonRead,
  depth: number,
): Within<{ value: "any"; store: "grow" }, Shown> {
  if (!isJsonList(labels)) return { top: false, atoms: ["(no type recorded)"] };
  if (
    labels.some((label) => {
      const row = rowAt(types, label);
      return isJsonList(row) && row.includes("source");
    })
  )
    return { top: true, atoms: [] };
  // Recognize literals by their definitions, not their row numbers: native
  // request graphs need not use the claims document's primitive prefix.
  const literalLabel = (value: boolean): JsonRead =>
    labels.find((label) => {
      const row = rowAt(types, label);
      const clause: JsonRead =
        isJsonList(row) && row.length === 1 ? row[0] : undefined;
      const boolLit = isJsonObject(clause) ? clause.boolLit : undefined;
      return isJsonObject(boolLit) && boolLit.value === value;
    });
  const trueLabel = literalLabel(true),
    falseLabel = literalLabel(false);
  const both = trueLabel !== undefined && falseLabel !== undefined;
  // The labels of a pair, each absent without the pair: a label is never
  // absent, so it matches neither then.
  const pairTrue = both ? trueLabel : undefined;
  const pairFalse = both ? falseLabel : undefined;
  // Each label's arms, lifted on demand: below the top, a union shows its
  // first `nestedArms` arms, and the arms past them are counted, not lifted.
  const armOf = (label: JsonValue): Within<{ value: "any"; store: "grow" }, { count: number; lift: (limit?: number) => Within<{ value: "any"; store: "grow" }, JsonValue[]> }> => {
    if (label === pairFalse) return { count: 0, lift: () => [] };
    if (label === pairTrue)
      return { count: 1, lift: () => [{ a: "boolean" }] };
    if (isJsonObject(label))
      return { count: 1, lift: () => [treeAtom(types, label, depth)] };
    if (isJsonList(label))
      return { count: 1, lift: () => ["type " + JSON.stringify(label)] };
    const name = typeof label === "number" ? types.names.get(label) : undefined;
    if (name !== undefined) {
      // The closure captures the name at the type the test gives it.
      const named: string = name;
      return { count: 1, lift: () => [named] };
    }
    const row = rowAt(types, label);
    if (!isJsonList(row))
      return { count: 1, lift: () => ["type " + stringOfJson(label)] };
    const clauses = row.flatMap(setLiterals);
    return {
      count: clauses.length,
      lift: (limit) => clauses.slice(0, limit).map((clause) => liftClause(types, clause, depth)),
    };
  };
  const arms = labels.map(armOf);
  const total = arms.reduce((n, arm) => n + arm.count, 0);
  if (depth < types.top && total > nestedArms) {
    const atoms: JsonValue[] = [];
    for (const arm of arms) {
      if (atoms.length >= nestedArms) break;
      atoms.push(...arm.lift(nestedArms - atoms.length));
    }
    return { top: false, atoms: [...atoms, "…"] };
  }
  return { top: false, atoms: arms.flatMap((arm) => arm.lift()) };
}

// A source-claims label tree names a row only the verifier builds, so it is
// shown by what it names: a binder by its name, an array over its store, an
// application by its declaration's position and its arguments, and an
// intersection as text, as an intersection of contracts is.
function treeAtom(
  types: Table,
  label: JsonObject,
  depth: number,
): Within<{ value: "any"; store: "grow" }, JsonValue> {
  const text = (labels: JsonValue): Within<{ value: "any"; store: "grow" }, string> =>
    textOf(liftType(types, labels, depth - 1));
  if (typeof label.binder === "string")
    return { a: "param", name: label.binder };
  if (isJsonList(label.array)) {
    const store = liftType(types, label.array, depth).atoms[0];
    if (isJsonObject(store) && store.a === "store") return { ...store, a: "array" };
  }
  if (typeof label.decl === "number")
    return (
      `declaration ${label.decl}` +
      (isJsonList(label.args)
        ? `<${label.args.map((arg) => text(arg)).join(", ")}>`
        : "")
    );
  if (isJsonList(label.meet))
    return label.meet.map((part) => `(${text(part)})`).join(" & ");
  return "type " + JSON.stringify(label);
}

// A type, lifted: the union of the labels, through a table whose application
// rows `names` spells, as a diagnostic's `names` does. The result is stated
// at `JsonValue`, the input of `printType`.
function lift(
  rows: JsonValue,
  labels: JsonValue,
  depth: number = 3,
  names: readonly (readonly [number, string])[] = [],
): JsonValue {
  return liftType(
    { rows, names: new Map(names), top: depth, lifted: new Map() },
    labels,
    depth,
  );
}

const same = (a: JsonValue, b: JsonValue): boolean =>
  JSON.stringify(a) === JSON.stringify(b);

const surfaceTypes: { printType: typeof printType; lift: typeof lift } = {
  printType,
  lift,
};

export default surfaceTypes;
