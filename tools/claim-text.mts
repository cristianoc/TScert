/* Surface text for the claim language declared in claim.mts, printed here so
 * reports and diagnostics share one syntax. @ followed by a JSON object states
 * nondefault object modes and conjunction metadata explicitly. The text always
 * determines its type. */
import { decodeClaimType, type Atom } from "./claim.mts";
import type { JsonObject, JsonRead, JsonValue } from "./calculus.mts";
import { passToolFailure } from "./thrown.mts";
import {
  numberOfBits,
  isArrayPresence,
  decodeCallEffect,
  ordinaryEffect,
  sameEffect,
  presencePrefix,
  type ClauseKey,
  type StringClause,
} from "./type-graph.mts";

/* What reaches the printers is the producer's, not this file's: a report shows
 * a claim that did not decode, and the lifter below names parts of a graph the
 * surface has no syntax for. Each is a value of `JsonValue`'s shape, so a read
 * here narrows what arrived rather than assuming a claim. */
function isObject(v: JsonRead): v is JsonObject {
  return typeof v === "object" && v !== null && !Array.isArray(v);
}
/** What a value holds: an object's values, an array's elements, a string's
 * characters; a primitive holds nothing. */
const members = (v: JsonValue): readonly JsonValue[] =>
  isObject(v)
    ? Object.values(v)
    : isList(v)
      ? v
      : typeof v === "string"
        ? [...v]
        : [];
/** An ordinary arrow's effect, the one a structural function atom states. */
const isOrdinary = (effect: JsonRead): boolean => {
  const decoded = decodeCallEffect(effect);
  return decoded !== undefined && sameEffect(decoded, ordinaryEffect);
};
/** A list where the producer sends one of records: an array of any
 * values, each checked where it is read. */
function isList(v: JsonRead): v is readonly JsonValue[] {
  return Array.isArray(v);
}
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
const isPrimitive = (v: JsonRead): v is BareKind<Atom> =>
  PRIMITIVE.some((p) => p === v);

/* ---------- printing ---------- */
/** Printing never fails; it records whether the text says the whole type. */
interface PrintState {
  printable: boolean;
}

/** The keys of an atom's metadata, literals naming no member of
 * `Object.prototype`. */
type MetadataKey = "call" | "construct" | "array";
function atomText(atom: JsonValue, state: PrintState): string {
  const text = bareAtomText(atom, state);
  if (!isObject(atom)) return text;
  const metadata: { [key: string]: JsonValue } = {};
  const keys: readonly MetadataKey[] = ["call", "construct", "array"];
  for (const key of keys) {
    const value = atom[key];
    if (value !== undefined && value !== "unknown") metadata[key] = value;
  }
  // Index markers other than all absent are shown, malformed ones too.
  const indexes = atom.indexes;
  if (indexes !== undefined && members(indexes).some((v) => v !== "absent"))
    metadata.indexes = indexes;
  const and = atom.and;
  if (and !== undefined) metadata.and = and;
  return Object.keys(metadata).length
    ? (atom.a === "function" ? "(" + text + ")" : text) +
        " @" +
        JSON.stringify(metadata)
    : text;
}
function bareAtomText(atom: JsonValue, state: PrintState): string {
  // An array where an atom belongs is no atom of any kind.
  if (isList(atom)) {
    state.printable = false;
    return "«type»";
  }
  if (!isObject(atom)) {
    state.printable = false;
    return String(atom);
  }
  if (atom.unsupported === true) {
    state.printable = false;
    return "(unavailable)";
  }
  if (isPrimitive(atom.a) && Object.keys(atom).join() === "a") return atom.a;
  if (
    (atom.a === "array" || atom.a === "store") &&
    isList(atom.required) &&
    isList(atom.optional)
  ) {
    // Both lists are read before a callback runs: `typeText` writes `state`,
    // and a field read after it is read at its contract.
    const requiredTypes = atom.required;
    const optionalTypes = atom.optional;
    const required = requiredTypes.map((t) => typeText(t, state));
    const optional = optionalTypes.map((t) => typeText(t, state) + "?");
    const rest = atom.rest === null ? null : typeText(atom.rest, state);
    const text =
      (isArrayPresence(atom.presence)
        ? presencePrefix(atom.presence)
        : "(invalid presence) ") +
      (required.length === 0 && optional.length === 0 && rest !== null
        ? `${atom.readonly ? "ReadonlyArray" : "Array"}<${rest}>`
        : `${atom.readonly ? "readonly " : ""}[${[...required, ...optional, ...(rest === null ? [] : [`...Array<${rest}>`])].join(", ")}]`);
    return atom.a === "store" ? `Store<${text}>` : text;
  }
  if (atom.a === "param" && typeof atom.name === "string") return atom.name;
  if (atom.a === "alias" && typeof atom.name === "string" && isList(atom.args))
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
    Number.isFinite(Number(atom.v))
  )
    return String(atom.v);
  if (atom.a === "bigintlit" && typeof atom.v === "string") return atom.v + "n";
  if (atom.a === "record" && isList(atom.fields)) {
    // An index signature that is no object is shown in the atom's encoding.
    if (isList(atom.indexSignature)) return JSON.stringify(atom);
    const index = isObject(atom.indexSignature) ? atom.indexSignature : null;
    const never = (t: JsonRead) =>
      isObject(t) && t.top === false && isList(t.atoms) && t.atoms.length === 0;
    if (index && !never(index.write)) return JSON.stringify(atom);
    return (
      "{ " +
      [
        ...atom.fields.map((field) => {
          // A field the producer sent malformed is shown as it is.
          if (!isObject(field))
            return "(invalid field " + JSON.stringify(field) + ")";
          // A name the surface can write is written, anything else quoted,
          // and a symbol key is shown by its index.
          const key = field.name;
          const name =
            (typeof key === "string"
              ? /^[A-Za-z_$][\w$]*$/.test(key)
                ? key
                : JSON.stringify(key)
              : isObject(key) && typeof key.symbol === "number"
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
  if (atom.a === "constructor" && isList(atom.params))
    return (
      "new (" +
      atom.params
        .map((p, i) => "arg" + i + ": " + typeText(p, state))
        .join(", ") +
      ") => " +
      typeText(atom.result, state)
    );
  if (atom.a === "function" && isList(atom.params)) {
    // The parameters are read before `typeText` writes `state`.
    const params = atom.params;
    return (
      "(" +
      [
        // A receiver-indifferent signature has no `this` to show.
        ...(isObject(atom.this) && atom.this.top === true
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
  return atom.a ? "«" + String(atom.a) + "»" : "«type»";
}

function typeText(type: JsonRead, state: PrintState): string {
  if (type === undefined || type === null) {
    state.printable = false;
    return "«missing»";
  }
  if (typeof type === "string") return type; // already a display string
  // Anything else is read for its fields, which a nonobject simply has none of.
  const shape: JsonObject = isObject(type) ? type : {};
  if (shape.unsupported === true) {
    state.printable = false;
    return "(unavailable)";
  }
  if (shape.top === true) return "unknown";
  const atoms: readonly JsonValue[] | null = isList(shape.atoms)
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
      const kind = isObject(atom) ? atom.a : undefined;
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
  top: boolean;
  atoms: JsonValue[];
};

/** A record field as a report shows it. */
type ShownField = {
  name: string;
  optional: boolean;
  read: Shown;
  write: Shown;
};

/** A record atom as a report shows it: its fields, and no index, call,
 * construct or array part. */
type ShownRecord = {
  a: "record";
  indexes: { string: "absent"; number: "absent"; symbol: "absent" };
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
): ShownRecord => {
  const entries: readonly JsonValue[] = isList(contract) ? contract : [];
  // A view field reads at its bound and accepts no write.
  const viewed: readonly JsonValue[] = isList(views) ? views : [];
  const readonly = viewed.map((entry) => {
    const pair: readonly JsonValue[] = isList(entry) ? entry : [];
    return {
      name: typeof pair[0] === "string" ? pair[0] : "",
      optional: false,
      read: liftType(types, pair[1], depth),
      write: { top: false, atoms: [] },
    };
  });
  return {
    a: "record",
    indexes: { string: "absent", number: "absent", symbol: "absent" },
    call: "unknown",
    construct: "unknown",
    array: "unknown",
    fields: [
      ...readonly,
      ...entries.map((entry) => {
        const pair: readonly JsonValue[] = isList(entry) ? entry : [];
        const invariant = pair[1];
        const name = typeof pair[0] === "string" ? pair[0] : "";
        return {
          name,
          optional: false,
          read: liftType(types, invariant, depth),
          write: liftType(types, invariant, depth),
        };
      }),
    ],
  };
};

// An intersection of contracts has no surface form; it is shown as text and
// stays on the JSON path, like anything else the surface cannot name.
const shown = (atoms: readonly JsonValue[]): string =>
  atoms
    .map((atom) => printType({ top: false, atoms: [atom] }).text)
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
  names: ReadonlyMap<number, string>;
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
const rowAt = (types: Table, label: JsonValue): JsonRead =>
  !isList(types.rows)
    ? undefined
    : typeof label === "number"
      ? types.rows[label]
      : typeof label === "string" && /^(0|[1-9][0-9]*)$/.test(label)
        ? types.rows[Number(label)]
        : undefined;

// A tag set's literal clauses; any other clause, itself.
function setLiterals(clause: JsonValue): JsonValue[] {
  if (isObject(clause) && isObject(clause.numIn) && isList(clause.numIn.bits))
    return clause.numIn.bits.map((bits) => ({ numLit: { bits } }));
  if (isObject(clause) && isObject(clause.strIn) && isList(clause.strIn.values))
    return clause.strIn.values.map((value) => ({ strLit: { value } }));
  return [clause];
}

/** A clause's encoding, which a report shows where the surface has no form
 * for it. A `JsonValue` serializes to a string; `undefined` is TypeScript's
 * result for other values. */
const encoding = (clause: JsonValue): string => JSON.stringify(clause) ?? "";

function liftClause(types: Table, clause: JsonValue, depth: number): JsonValue {
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
    isObject(clause) ? clause[key] : undefined;
  const boolLit = body("boolLit");
  if (boolLit)
    return {
      a: "booleanlit",
      v: String(isObject(boolLit) ? boolLit.value : undefined),
    };
  // The surface names the number, not the bit pattern that identifies it.
  const numLit = body("numLit");
  if (numLit)
    return {
      a: "numberlit",
      v: String(
        numberOfBits(String(isObject(numLit) ? numLit.bits : undefined)),
      ),
    };
  const bigintLit = body("bigintLit");
  if (bigintLit)
    return {
      a: "bigintlit",
      v: String(isObject(bigintLit) ? bigintLit.value : undefined),
    };
  // A symbol singleton has no claim form; the reader names it.
  const symbolLit = body("symbolLit");
  if (symbolLit)
    return `unique symbol ${String(isObject(symbolLit) ? symbolLit.id : undefined)}`;
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
      v: String(isObject(strLit) ? strLit.value : undefined),
    };
  // The graph is finite but may be cyclic, so lifting stops rather than recursing.
  if (depth <= 0) return "…";
  const list = body("list");
  if (isObject(list) && isObject(list.first) && isList(list.rest)) {
    const t = list.first;
    // Read before `liftType`, which writes `types.lifted`, runs.
    const required = t.required;
    const optional = t.optional;
    if (list.rest.length || !isList(required) || !isList(optional))
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
    const first = isObject(refs) ? refs.first : undefined;
    const rest: readonly JsonValue[] =
      isObject(refs) && isList(refs.rest) ? refs.rest : [];
    const views = isObject(refs) ? refs.views : undefined;
    const cells = [first, ...rest].map((c, i) =>
      cell(types, c, depth - 1, i === 0 ? views : []),
    );
    const [only] = cells;
    if (only === undefined || cells.length !== 1) return shown(cells);
    const [f] = only.fields;
    if (f !== undefined && only.fields.length === 1) {
      const store = f.read.atoms[0];
      if (
        f.name === "[]" &&
        isObject(store) &&
        store.a === "store" &&
        ((same(f.read, f.write) && store.readonly === false) ||
          (f.write.atoms.length === 0 && store.readonly === true))
      )
        return { ...store, a: "array" };
    }
    return only;
  }
  const dict = body("dict");
  if (isObject(dict)) {
    const indexes: readonly JsonValue[] = isList(dict.indexes)
      ? dict.indexes
      : [];
    const index: JsonRead = indexes[0];
    if (
      !isList(dict.rest) ||
      dict.rest.length ||
      !isList(dict.indexes) ||
      indexes.length !== 1 ||
      !isList(index) ||
      index.length !== 2
    )
      return encoding(clause);
    const record = cell(types, dict.first, depth - 1, dict.views);
    return {
      ...record,
      indexSignature: {
        read: liftType(types, index[1], depth - 1),
        write: { top: false, atoms: [] },
      },
    };
  }
  const callable = body("callable");
  if (callable) {
    const c: JsonObject = isObject(callable) ? callable : {};
    const rest: readonly JsonValue[] = isList(c.rest) ? c.rest : [];
    const fixed: readonly JsonValue[] = isList(c.arrows) ? c.arrows : [];
    const variadic: readonly JsonValue[] = isList(c.variadic) ? c.variadic : [];
    if (
      [...fixed, ...variadic].some((s) => !isObject(s) || !isOrdinary(s.effect))
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
  if (isObject(arrs)) {
    const fixed: readonly JsonValue[] = isList(arrs.arrows) ? arrs.arrows : [];
    const variadic: readonly JsonValue[] = isList(arrs.variadic)
      ? arrs.variadic
      : [];
    if (
      [...fixed, ...variadic].some((s) => !isObject(s) || !isOrdinary(s.effect))
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
): JsonObject[] {
  const atom = (
    receiver: JsonRead,
    domain: JsonRead,
    result: JsonRead,
    element?: JsonRead,
  ): JsonObject => {
    const domains: readonly JsonValue[] = isList(domain) ? domain : [];
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
  const arrows: readonly JsonValue[] = isList(fixed) ? fixed : [];
  const sigs: readonly JsonValue[] = isList(variadic) ? variadic : [];
  return [
    ...arrows.map((arrow) => {
      if (!isObject(arrow) || !isOrdinary(arrow.effect))
        throw new TypeSyntaxError(
          "a qualified signature has no structural form",
        );
      return atom(arrow.receiver, arrow.arguments, arrow.result);
    }),
    ...sigs.map((sig) => {
      if (!isObject(sig) || !isOrdinary(sig.effect))
        throw new TypeSyntaxError(
          "a qualified signature has no structural form",
        );
      const [domain, rest]: readonly JsonRead[] = isList(sig.arguments)
        ? sig.arguments
        : [];
      return atom(sig.receiver, domain, sig.result, restElement(types, rest));
    }),
  ];
}

/** The element of an element rest: a type whose one clause is the pack of
any number of actuals at it. Any other rest type is shown as itself. */
function restElement(types: Table, rest: JsonRead): JsonRead {
  if (!isList(rest) || rest.length !== 1) return rest;
  const [label] = rest;
  const row = label === undefined ? undefined : rowAt(types, label);
  const clause: JsonRead = isList(row) && row.length === 1 ? row[0] : undefined;
  const pack = isObject(clause) ? clause.pack : undefined;
  if (!isObject(pack) || !isList(pack.rest) || pack.rest.length) return rest;
  const t = pack.first;
  if (
    !isObject(t) ||
    !isList(t.required) ||
    t.required.length ||
    !isList(t.optional) ||
    t.optional.length ||
    t.readonly !== false ||
    t.rest === null
  )
    return rest;
  return t.rest;
}

// A lift is a function of its labels and depth within one table, so a label
// list lifted once at a depth is reused there.
function liftType(types: Table, labels: JsonRead, depth: number): Shown {
  const at = `${depth}:${JSON.stringify(labels)}`;
  const held = types.lifted.get(at);
  if (held !== undefined) return held;
  const lifted = liftLabels(types, labels, depth);
  types.lifted.set(at, lifted);
  return lifted;
}

function liftLabels(types: Table, labels: JsonRead, depth: number): Shown {
  if (!isList(labels)) return { top: false, atoms: ["(no type recorded)"] };
  if (
    labels.some((label) => {
      const row = rowAt(types, label);
      return isList(row) && row.includes("source");
    })
  )
    return { top: true, atoms: [] };
  // Recognize literals by their definitions, not their row numbers: native
  // request graphs need not use the claims document's primitive prefix.
  const literalLabel = (value: boolean): JsonRead =>
    labels.find((label) => {
      const row = rowAt(types, label);
      const clause: JsonRead =
        isList(row) && row.length === 1 ? row[0] : undefined;
      const boolLit = isObject(clause) ? clause.boolLit : undefined;
      return isObject(boolLit) && boolLit.value === value;
    });
  const trueLabel = literalLabel(true),
    falseLabel = literalLabel(false);
  const both = trueLabel !== undefined && falseLabel !== undefined;
  // Each label's arms, lifted on demand: below the top, a union shows its
  // first `nestedArms` arms, and the arms past them are counted, not lifted.
  const arms = labels.map((label): { count: number; lift: (limit?: number) => JsonValue[] } => {
    if (both && label === falseLabel) return { count: 0, lift: () => [] };
    if (both && label === trueLabel)
      return { count: 1, lift: () => [{ a: "boolean" }] };
    if (isObject(label))
      return { count: 1, lift: () => [treeAtom(types, label, depth)] };
    if (isList(label))
      return { count: 1, lift: () => ["type " + JSON.stringify(label)] };
    const name = typeof label === "number" ? types.names.get(label) : undefined;
    if (name !== undefined) return { count: 1, lift: () => [name] };
    const row = rowAt(types, label);
    if (!isList(row))
      return { count: 1, lift: () => ["type " + String(label)] };
    const clauses = row.flatMap(setLiterals);
    return {
      count: clauses.length,
      lift: (limit) => clauses.slice(0, limit).map((clause) => liftClause(types, clause, depth)),
    };
  });
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
function treeAtom(types: Table, label: JsonObject, depth: number): JsonValue {
  const text = (labels: JsonValue) =>
    printType(liftType(types, labels, depth - 1)).text;
  if (typeof label.binder === "string")
    return { a: "param", name: label.binder };
  if (isList(label.array)) {
    const store = liftType(types, label.array, depth).atoms[0];
    if (isObject(store) && store.a === "store") return { ...store, a: "array" };
  }
  if (typeof label.decl === "number")
    return (
      `declaration ${label.decl}` +
      (isList(label.args)
        ? `<${label.args.map((arg) => text(arg)).join(", ")}>`
        : "")
    );
  if (isList(label.meet))
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
