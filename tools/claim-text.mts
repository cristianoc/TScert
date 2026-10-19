/* Surface text for the claim language declared in claim.mts, printed here so
 * reports and diagnostics share one syntax. @ followed by a JSON object states
 * nondefault object modes and conjunction metadata explicitly. The text always
 * determines its type. */
import { decodeClaimType, type Atom } from "./claim.mts";
import {
  numberOfBits,
  isArrayPresence,
  isCallEffect,
  ordinaryEffect,
  sameEffect,
  presencePrefix,
  type ClauseKey,
  type StringClause,
} from "./type-graph.mts";

/* What reaches the printers is the producer's, not this file's: a report shows
 * a claim that did not decode, and the lifter below names parts of a graph the
 * surface has no syntax for. So a read here narrows what arrived rather than
 * assuming a claim. */
function isObject(v: unknown): v is Record<string, unknown> {
  return v !== null && typeof v === "object";
}
/** An ordinary arrow's effect, the one a structural function atom states. */
const isOrdinary = (effect: unknown): boolean => isCallEffect(effect) && sameEffect(effect, ordinaryEffect);
/** A list of records where the producer sends one: each element is checked
 * to be an object, so a list holding anything else is not one. */
function isRecordList(v: unknown): v is Record<string, unknown>[] {
  return Array.isArray(v) && v.every((e: unknown) => isObject(e));
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
const isPrimitive = (v: unknown): v is BareKind<Atom> =>
  PRIMITIVE.some((p) => p === v);

/* ---------- printing ---------- */
/** Printing never fails; it records whether the text says the whole type. */
interface PrintState {
  printable: boolean;
}

function atomText(atom: unknown, state: PrintState): string {
  const text = bareAtomText(atom, state);
  if (!isObject(atom)) return text;
  const metadata: Record<string, unknown> = {};
  for (const key of ["call", "construct", "array"])
    if (key in atom && atom[key] !== "unknown") metadata[key] = atom[key];
  if (atom.indexes && Object.values(atom.indexes).some((v: unknown) => v !== "absent"))
    metadata.indexes = atom.indexes;
  if (atom.and !== undefined) metadata.and = atom.and;
  return Object.keys(metadata).length
    ? (atom.a === "function" ? "(" + text + ")" : text) +
        " @" +
        JSON.stringify(metadata)
    : text;
}
function bareAtomText(atom: unknown, state: PrintState): string {
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
    Array.isArray(atom.required) &&
    Array.isArray(atom.optional)
  ) {
    const required = atom.required.map((t: unknown) => typeText(t, state));
    const optional = atom.optional.map((t: unknown) => typeText(t, state) + "?");
    const rest = atom.rest === null ? null : typeText(atom.rest, state);
    const text = (isArrayPresence(atom.presence) ? presencePrefix(atom.presence) : "(invalid presence) ") + (
      required.length === 0 && optional.length === 0 && rest !== null
        ? `${atom.readonly ? "ReadonlyArray" : "Array"}<${rest}>`
        : `${atom.readonly ? "readonly " : ""}[${[...required, ...optional, ...(rest === null ? [] : [`...Array<${rest}>`])].join(", ")}]`);
    return atom.a === "store" ? `Store<${text}>` : text;
  }
  if (atom.a === "param" && typeof atom.name === "string") return atom.name;
  if (
    atom.a === "alias" &&
    typeof atom.name === "string" &&
    Array.isArray(atom.args)
  )
    return (
      atom.name +
      "<" +
      atom.args.map((t: unknown) => typeText(t, state)).join(", ") +
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
  if (atom.a === "record" && isRecordList(atom.fields)) {
    const index = isObject(atom.indexSignature) ? atom.indexSignature : null;
    const never = (t: unknown) =>
      isObject(t) &&
      t.top === false &&
      Array.isArray(t.atoms) &&
      t.atoms.length === 0;
    if (index && !never(index.write)) return JSON.stringify(atom);
    return (
      "{ " +
      [
        ...atom.fields.map((field) => {
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
  if (atom.a === "constructor" && Array.isArray(atom.params))
    return (
      "new (" +
      atom.params.map((p: unknown, i: number) => "arg" + i + ": " + typeText(p, state)).join(", ") +
      ") => " +
      typeText(atom.result, state)
    );
  if (atom.a === "function" && Array.isArray(atom.params))
    return (
      "(" +
      [
        // A receiver-indifferent signature has no `this` to show.
        ...(isObject(atom.this) && atom.this.top === true
          ? []
          : ["this: " + typeText(atom.this, state)]),
        ...atom.params.map((p: unknown) => typeText(p, state)),
        ...(atom.rest === undefined
          ? []
          : ["...Array<" + typeText(atom.rest, state) + ">"]),
      ].join(", ") +
      ") => " +
      typeText(atom.result, state)
    );
  state.printable = false;
  return atom.a ? "«" + String(atom.a) + "»" : "«type»";
}

function typeText(type: unknown, state: PrintState): string {
  if (type === undefined || type === null) {
    state.printable = false;
    return "«missing»";
  }
  if (typeof type === "string") return type; // already a display string
  // Anything else is read for its fields, which a nonobject simply has none of.
  const shape: Record<string, unknown> = isObject(type) ? type : {};
  if (shape.unsupported === true) {
    state.printable = false;
    return "(unavailable)";
  }
  if (shape.top === true) return "unknown";
  const atoms: unknown[] | null = Array.isArray(shape.atoms)
    ? shape.atoms
    : null;
  if (!atoms) {
    state.printable = false;
    return "«type»";
  }
  if (!atoms.length) return "never";
  return atoms
    .map((atom: unknown) => {
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

function printType(type: unknown): Printed {
  const state: PrintState = { printable: true };
  try {
    decodeClaimType(type);
  } catch {
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
 * text where an atom belongs. The printers above take that in stride. */
interface Shown {
  top: boolean;
  atoms: unknown[];
}

/** A record field as a report shows it. */
interface ShownField {
  name: string;
  optional: boolean;
  read: Shown;
  write: Shown;
}

/** A record atom as a report shows it: its fields, and no index, call,
 * construct or array part. */
interface ShownRecord {
  a: "record";
  indexes: { string: "absent"; number: "absent"; symbol: "absent" };
  call: "unknown";
  construct: "unknown";
  array: "unknown";
  fields: ShownField[];
}

/** A record contract's fields, as the claim language writes them: each field
 * reads and writes at its own invariant. */
const cell = (
  types: Table,
  contract: unknown,
  depth: number,
  views: unknown = [],
): ShownRecord => {
  const entries: unknown[] = Array.isArray(contract) ? contract : [];
  // A view field reads at its bound and accepts no write.
  const viewed: unknown[] = Array.isArray(views) ? views : [];
  const readonly = viewed.map((entry) => {
    const pair: unknown[] = Array.isArray(entry) ? entry : [];
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
        const pair: unknown[] = Array.isArray(entry) ? entry : [];
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
const shown = (atoms: unknown[]): string =>
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
  rows: unknown;
  names: ReadonlyMap<number, string>;
}

// A row, where the table has one under that label. Both arrive from the
// document, so neither is trusted to be there.
const rowAt = (types: Table, label: unknown): unknown =>
  Array.isArray(types.rows) &&
  (typeof label === "number" || typeof label === "string")
    ? Object.getOwnPropertyDescriptor(types.rows, label)?.value
    : undefined;

// A tag set's literal clauses; any other clause, itself.
function setLiterals(clause: unknown): unknown[] {
  if (isObject(clause) && isObject(clause.numIn) && Array.isArray(clause.numIn.bits))
    return clause.numIn.bits.map((bits: unknown) => ({ numLit: { bits } }));
  if (isObject(clause) && isObject(clause.strIn) && Array.isArray(clause.strIn.values))
    return clause.strIn.values.map((value: unknown) => ({ strLit: { value } }));
  return [clause];
}

function liftClause(types: Table, clause: unknown, depth: number): unknown {
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
  // says these are all of them; here the key is only read.
  const body = (key: string): unknown =>
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
    return setLiterals(clause).map((c) => JSON.stringify(liftClause(types, c, depth))).join(" | ");
  const strLit = body("strLit");
  if (strLit)
    return {
      a: "stringlit",
      v: String(isObject(strLit) ? strLit.value : undefined),
    };
  // The graph is finite but may be cyclic, so lifting stops rather than recursing.
  if (depth <= 0) return "…";
  const list = body("list");
  if (isObject(list) && isObject(list.first) && Array.isArray(list.rest)) {
    const t = list.first;
    if (
      list.rest.length ||
      !Array.isArray(t.required) ||
      !Array.isArray(t.optional)
    )
      return JSON.stringify(clause);
    return {
      a: "store",
      required: t.required.map((a: unknown) => liftType(types, a, depth - 1)),
      optional: t.optional.map((a: unknown) => liftType(types, a, depth - 1)),
      rest: t.rest === null ? null : liftType(types, t.rest, depth - 1),
      readonly: t.readonly,
      presence: t.presence,
    };
  }
  const refs = body("refs");
  if (refs) {
    const first = isObject(refs) ? refs.first : undefined;
    const rest: unknown[] =
      isObject(refs) && Array.isArray(refs.rest) ? refs.rest : [];
    const views = isObject(refs) ? refs.views : undefined;
    const cells = [first, ...rest].map((c, i) =>
      cell(types, c, depth - 1, i === 0 ? views : []),
    );
    if (cells.length === 1 && cells[0].fields.length === 1) {
      const f = cells[0].fields[0];
      const store =
        isObject(f.read) && Array.isArray(f.read.atoms)
          ? f.read.atoms[0]
          : undefined;
      if (
        f.name === "[]" &&
        isObject(store) &&
        store.a === "store" &&
        ((same(f.read, f.write) && store.readonly === false) ||
          (isObject(f.write) &&
            Array.isArray(f.write.atoms) &&
            f.write.atoms.length === 0 &&
            store.readonly === true))
      )
        return { ...store, a: "array" };
    }
    return cells.length === 1 ? cells[0] : shown(cells);
  }
  const dict = body("dict");
  if (isObject(dict)) {
    const indexes: unknown[] = Array.isArray(dict.indexes) ? dict.indexes : [];
    const index: unknown = indexes[0];
    if (
      !Array.isArray(dict.rest) ||
      dict.rest.length ||
      !Array.isArray(dict.indexes) ||
      indexes.length !== 1 ||
      !Array.isArray(index) ||
      index.length !== 2
    )
      return JSON.stringify(clause);
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
    const c: Record<string, unknown> = isObject(callable) ? callable : {};
    const rest: unknown[] = Array.isArray(c.rest) ? c.rest : [];
    const fixed: unknown[] = Array.isArray(c.arrows) ? c.arrows : [];
    const variadic: unknown[] = Array.isArray(c.variadic) ? c.variadic : [];
    if ([...fixed, ...variadic].some(
        (s: unknown) => !isObject(s) || !isOrdinary(s.effect))) return JSON.stringify(clause);
    const signatures = liftSignatures(types, c.arrows, c.variadic, depth);
    if (rest.length || signatures.length !== 1) return JSON.stringify(clause);
    return {
      a: "callable",
      function: signatures[0],
      bag: cell(types, c.first, depth - 1),
    };
  }
  const arrs = body("arrs");
  if (isObject(arrs)) {
    const fixed: unknown[] = Array.isArray(arrs.arrows) ? arrs.arrows : [];
    const variadic: unknown[] = Array.isArray(arrs.variadic) ? arrs.variadic : [];
    if ([...fixed, ...variadic].some(
        (s: unknown) => !isObject(s) || !isOrdinary(s.effect))) return JSON.stringify(clause);
    const arrows = liftSignatures(types, arrs.arrows, arrs.variadic, depth);
    if (arrows.length) return arrows.length === 1 ? arrows[0] : shown(arrows);
  }
  // Unknown clauses are shown as their encoding rather than guessed at.
  return JSON.stringify(clause);
}

/** A clause's call signatures as function atoms: its fixed arrows, then its
variadic ones, whose further actuals are at `rest`: an element rest's element,
or the rest type itself when it is no element rest. */
function liftSignatures(
  types: Table,
  fixed: unknown,
  variadic: unknown,
  depth: number,
): Record<string, unknown>[] {
  const atom = (
    receiver: unknown,
    domain: unknown,
    result: unknown,
    element?: unknown,
  ) => {
    const domains: unknown[] = Array.isArray(domain) ? domain : [];
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
  const arrows: unknown[] = Array.isArray(fixed) ? fixed : [];
  const sigs: unknown[] = Array.isArray(variadic) ? variadic : [];
  return [
    ...arrows.map((arrow) => {
      if (!isObject(arrow) || !isOrdinary(arrow.effect))
        throw new TypeSyntaxError("a qualified signature has no structural form");
      return atom(arrow.receiver, arrow.arguments, arrow.result);
    }),
    ...sigs.map((sig) => {
      if (!isObject(sig) || !isOrdinary(sig.effect))
        throw new TypeSyntaxError("a qualified signature has no structural form");
      const [domain, rest]: unknown[] = Array.isArray(sig.arguments) ? sig.arguments : [];
      return atom(sig.receiver, domain, sig.result, restElement(types, rest));
    }),
  ];
}

/** The element of an element rest: a type whose one clause is the pack of
any number of actuals at it. Any other rest type is shown as itself. */
function restElement(types: Table, rest: unknown): unknown {
  if (!Array.isArray(rest) || rest.length !== 1) return rest;
  const row = rowAt(types, rest[0]);
  const clause: unknown = Array.isArray(row) && row.length === 1 ? row[0] : undefined;
  const pack = isObject(clause) ? clause.pack : undefined;
  if (!isObject(pack) || !Array.isArray(pack.rest) || pack.rest.length) return rest;
  const t = pack.first;
  if (
    !isObject(t) ||
    !Array.isArray(t.required) ||
    t.required.length ||
    !Array.isArray(t.optional) ||
    t.optional.length ||
    t.readonly !== false ||
    t.rest === null
  )
    return rest;
  return t.rest;
}

function liftType(types: Table, labels: unknown, depth: number): Shown {
  if (!Array.isArray(labels))
    return { top: false, atoms: ["(no type recorded)"] };
  if (
    labels.some((label: unknown) => {
      const row = rowAt(types, label);
      return Array.isArray(row) && row.includes("source");
    })
  )
    return { top: true, atoms: [] };
  // Recognize literals by their definitions, not their row numbers: native
  // request graphs need not use the claims document's primitive prefix.
  const literalLabel = (value: boolean): unknown =>
    labels.find((label: unknown) => {
      const row = rowAt(types, label);
      const clause: unknown =
        Array.isArray(row) && row.length === 1 ? row[0] : undefined;
      const boolLit = isObject(clause) ? clause.boolLit : undefined;
      return isObject(boolLit) && boolLit.value === value;
    });
  const trueLabel = literalLabel(true),
    falseLabel = literalLabel(false);
  const both = trueLabel !== undefined && falseLabel !== undefined;
  const atoms = labels.flatMap((label: unknown) => {
    if (both && label === falseLabel) return [];
    if (both && label === trueLabel) return [{ a: "boolean" }];
    if (isObject(label)) return [treeAtom(types, label, depth)];
    const name = typeof label === "number" ? types.names.get(label) : undefined;
    if (name !== undefined) return [name];
    const row = rowAt(types, label);
    if (!Array.isArray(row)) return ["type " + String(label)];
    return row.flatMap(setLiterals).map((clause: unknown) => liftClause(types, clause, depth));
  });
  return { top: false, atoms };
}

// A source-claims label tree names a row only the verifier builds, so it is
// shown by what it names: a binder by its name, an array over its store, an
// application by its declaration's position and its arguments, and an
// intersection as text, as an intersection of contracts is.
function treeAtom(types: Table, label: Record<string, unknown>, depth: number): unknown {
  const text = (labels: unknown) => printType(liftType(types, labels, depth - 1)).text;
  if (typeof label.binder === "string") return { a: "param", name: label.binder };
  if (Array.isArray(label.array)) {
    const store = liftType(types, label.array, depth).atoms[0];
    if (isObject(store) && store.a === "store") return { ...store, a: "array" };
  }
  if (typeof label.decl === "number")
    return `declaration ${label.decl}` +
      (Array.isArray(label.args) ? `<${label.args.map(text).join(", ")}>` : "");
  if (Array.isArray(label.meet)) return label.meet.map((part: unknown) => `(${text(part)})`).join(" & ");
  return "type " + JSON.stringify(label);
}

// A type, lifted: the union of the labels, through a table whose application
// rows `names` spells, as a diagnostic's `names` does.
function lift(
  rows: unknown,
  labels: unknown,
  depth: number = 3,
  names: readonly (readonly [number, string])[] = [],
): Shown {
  return liftType({ rows, names: new Map(names) }, labels, depth);
}

const same = (a: unknown, b: unknown): boolean =>
  JSON.stringify(a) === JSON.stringify(b);

const surfaceTypes: { printType: typeof printType; lift: typeof lift } = {
  printType,
  lift,
};

export default surfaceTypes;
