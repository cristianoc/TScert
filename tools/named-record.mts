/** A named type's outer record shape, which a mapped type whose value is
 * `X[P]` maps at a named X (SOURCE-CONTRACTS.md, "Library types", the rule
 * mapped-identity), and the settling of mapped types read before the
 * definitions they reach were complete. Both readers use it: the
 * declaration graph once its collection ends, and the gate for the file's
 * annotations, read after the declaration document is complete. */
import type { DeclarationIdentity, PropertyKey, TypeDefinition, TypeTerm, ValueRoot, WrittenApplication } from "./declaration-types.mts";
import { DEFERRED_MODULE, deferredOf, expandMapped, substitute, type TermScope } from "./type-term.mts";

type Reference = Extract<TypeTerm, { k: "reference" }>;
type ObjectTerm = Extract<TypeTerm, { k: "object" }>;
type Fail = (message: string) => never;

/** A definition's key: its full declaration identity. */
export const definitionKey = (id: DeclarationIdentity): Within<{ value: "any"; store: "grow" }, string> =>
  JSON.stringify([id.module, id.span, id.name]);

/** The complete definitions a shape is read from: each by its identity,
 * and whether it is a record, an interface or a type alias read as its
 * declared body outside a host type, or an alias of a named type
 * (`records` of the declaration graph);
 * a class, a host type, a library interface read through its overlay or a
 * definition the reader states itself is none. */
export type NamedRecords = {
  definition(id: DeclarationIdentity, fail: Fail): Within<{ value: "any"; store: "grow" }, TypeDefinition | undefined>;
  record(id: DeclarationIdentity): Within<{ value: "any"; store: "grow" }, boolean>;
};

const PREFIX = "a mapped type's value names its key, over a named type";

/** Whether two terms are the same type, their spans aside. */
const sameTerm = (a: unknown, b: unknown): Within<{ value: "any"; store: "grow" }, boolean> => {
  const text = (t: unknown): string => JSON.stringify(t, function (this: unknown, key: string, value: unknown) {
    // A declaration identity's span is the declaration's; any other span,
    // and a reference's argument spans, only locate the term.
    const identity = typeof this === "object" && this !== null && "module" in this;
    return (key === "span" && !identity) || (key === "arguments" && typeof this === "object" && this !== null && "target" in this)
      ? undefined : value;
  }) ?? "";
  return text(a) === text(b);
};

const keyText = (name: PropertyKey): Within<{ value: "any"; store: "grow" }, string> =>
  typeof name === "string" ? name : `[symbol ${name.symbol}]`;

/** The outer record shape `reference` names: the record its definition's
 * equation is at the reference's arguments, an alias followed to its
 * equation, with the members of every base, transitively. One unfolding
 * only: the fields keep the types they are declared at, references
 * included. A shape reaching itself, a definition that is no record, call
 * or construct signatures, a prototype or a host's members, and an inherited
 * member or index redeclared at another type are refused. */
export function recordShape(reference: Reference, records: NamedRecords, fail: Fail): Within<{ value: "any"; store: "grow" }, ObjectTerm> {
  const named = (ref: Reference, path: readonly string[]): ObjectTerm => {
    const target = ref.reference.target;
    const key = definitionKey(target);
    const name = `${target.module}#${target.name}`;
    if (path.includes(key)) return fail(`${PREFIX} whose shape reaches itself through its equation or its bases: ${name}`);
    if (!records.record(target))
      return fail(`${PREFIX} that is no record written as one (a class, a host type or a type the library reads at its meaning): ${name}`);
    const definition = records.definition(target, fail) ?? fail(`${PREFIX} with no definition: ${name}`);
    if (definition.parameters.length !== ref.args.length) return fail(`${PREFIX} applied at ${ref.args.length} of its ${definition.parameters.length} parameters: ${name}`);
    if (!definition.expression) return fail(`${PREFIX} with no equation the reader holds: ${name}`);
    const inner = [...path, key];
    const own = outer(substitute(definition.expression, ref.args), inner, name);
    return definition.bases.reduce<ObjectTerm>((shape, base) =>
      inherit(shape, outer(substitute(base, ref.args), inner, name), name), own);
  };
  const outer = (term: TypeTerm, path: readonly string[], name: string): ObjectTerm => {
    if (term.k === "reference") {
      if (deferredOf(term)) return fail(`${PREFIX} whose definition is not settled: ${name}`);
      return named(term, path);
    }
    if (term.k !== "object") return fail(`${PREFIX} that is no record (${term.k === "atom" ? term.name : `a ${term.k}`}): ${name}`);
    if (term.calls.length) return fail(`${PREFIX} with call signatures: ${name}`);
    if (term.prototype || term.host || term.stable) return fail(`${PREFIX} with a prototype or a host's members: ${name}`);
    return term;
  };
  // An interface's own members first, then each base's: one declared by both
  // is admitted where it is the same member, modifiers included.
  const inherit = (own: ObjectTerm, base: ObjectTerm, name: string): ObjectTerm => {
    const fields = [...own.fields];
    for (const field of base.fields) {
      const declared = fields.find(f => keyText(f.name) === keyText(field.name));
      if (!declared) fields.push(field);
      else if (!sameTerm({ ...declared, span: null }, { ...field, span: null }))
        fail(`${PREFIX} that redeclares its base's member ${keyText(field.name)} at another type or modifier: ${name}`);
    }
    const index = <I,>(mine: I | null | undefined, theirs: I | null | undefined, what: string): I | null => {
      if (!theirs) return mine ?? null;
      if (!mine) return theirs;
      if (!sameTerm(mine, theirs)) fail(`${PREFIX} that redeclares its base's ${what} index at another type or modifier: ${name}`);
      return mine;
    };
    const numberIndex = index(own.numberIndex, base.numberIndex, "number");
    const symbolIndex = index(own.symbolIndex, base.symbolIndex, "symbol");
    return { ...own, fields, stringIndex: index(own.stringIndex, base.stringIndex, "string"),
      ...(numberIndex ? { numberIndex } : {}), ...(symbolIndex ? { symbolIndex } : {}) };
  };
  return named(reference, []);
}

/** A term's parts each mapped by `go`. */
function mapParts(term: TypeTerm, go: (part: TypeTerm) => Within<{ value: "any"; store: "grow" }, TypeTerm>): Within<{ value: "any"; store: "grow" }, TypeTerm> {
  type FunctionTerm = Extract<TypeTerm, { k: "function" }>;
  const fn = (f: FunctionTerm): FunctionTerm => ({ ...f, receiver: f.receiver && go(f.receiver),
    params: f.params.map(go), rest: f.rest && go(f.rest), result: go(f.result) });
  switch (term.k) {
    case "atom": case "literal": case "unique": case "self": case "binder": case "callable": case "parameter": return term;
    case "union": case "intersection": return { ...term, parts: term.parts.map(go) };
    case "array": return { ...term, element: go(term.element) };
    case "tuple": return { ...term, required: term.required.map(go), optional: term.optional.map(go),
      rest: term.rest && go(term.rest) };
    case "object": return { ...term, fields: term.fields.map(f => ({ ...f, type: go(f.type) })),
      stringIndex: term.stringIndex && { ...term.stringIndex, value: go(term.stringIndex.value) },
      ...(term.numberIndex ? { numberIndex: { ...term.numberIndex, value: go(term.numberIndex.value) } } : {}),
      ...(term.symbolIndex ? { symbolIndex: { ...term.symbolIndex, value: go(term.symbolIndex.value) } } : {}),
      ...(term.prototype ? { prototype: go(term.prototype) } : {}),
      calls: term.calls.map(fn) };
    case "function": return fn(term);
    case "constructor": return { ...term, params: term.params.map(go), rest: term.rest && go(term.rest),
      result: go(term.result), ...(term.statics ? { statics: term.statics.map(s => ({ ...s, type: go(s.type) })) } : {}) };
    case "pack": return { ...term, of: go(term.of) };
    case "scheme": return { ...term, binders: term.binders.map(b => ({ ...b, bound: b.bound && go(b.bound),
      default: b.default && go(b.default) })), signatures: term.signatures.map(f => f.k === "function" ? fn(f)
        : { ...f, params: f.params.map(go), rest: f.rest && go(f.rest), result: go(f.result) }) };
    case "reference": return { ...term, args: term.args.map(go) };
  }
}

/** Every deferred mapped type of a declaration document's definitions,
 * values and applications replaced by its expansion at the complete
 * definitions (`settleTerm`): each definition settled once, before a
 * shape is read from it, so a definition whose settling needs its own shape
 * is refused. `refused` is told a refusal, with where it was met, and gives
 * the term to continue with (a diagnostic run's), or throws. */
export function settleDocument(document: { definitions: TypeDefinition[]; values: ValueRoot[]; applications: WrittenApplication[] },
    record: (id: DeclarationIdentity) => Within<{ value: "any"; store: "grow" }, boolean>,
    refused: (where: string, error: unknown) => Within<{ value: "any"; store: "grow" }, TypeTerm>): Within<{ value: "any"; store: "grow" }, { definitions: TypeDefinition[]; values: ValueRoot[]; applications: WrittenApplication[] }> {
  const byKey = new Map(document.definitions.map(d => [definitionKey(d.declaration), d] as const));
  const settled = new Map<string, TypeDefinition>();
  const settling = new Set<string>();
  const records: NamedRecords = {
    record,
    definition: (id, fail) => {
      const key = definitionKey(id);
      if (settling.has(key)) return fail(`${PREFIX} whose shape is read while its own definition is settled: ${id.module}#${id.name}`);
      const found = byKey.get(key);
      return found && settle(found);
    },
  };
  const term = (t: TypeTerm, where: string): TypeTerm => settleTerm(t, records, where, refused);
  const settle = (d: TypeDefinition): TypeDefinition => {
    const key = definitionKey(d.declaration);
    const done = settled.get(key);
    if (done) return done;
    settling.add(key);
    const where = `${d.declaration.module}#${d.declaration.name}`;
    const result = { ...d, bases: d.bases.map(b => term(b, where)), expression: d.expression && term(d.expression, where) };
    settling.delete(key);
    settled.set(key, result);
    return result;
  };
  const definitions = document.definitions.map(settle);
  const parameter = <P extends { bound: TypeTerm | null },>(p: P, where: string): P => ({ ...p, bound: p.bound && term(p.bound, where) });
  const values = document.values.map(v => {
    const where = `the type of ${v.binding.local}`;
    return { ...v, typeParams: v.typeParams.map(p => parameter(p, where)), type: term(v.type, where) };
  });
  const applications = document.applications.map(a => ({ ...a, scope: a.scope.map(g => g.map(p => parameter(p, a.site))),
    args: a.args.map(t => term(t, a.site)), bounds: a.bounds.map(t => t && term(t, a.site)) }));
  return { definitions, values, applications };
}

/** `term` with each deferred mapped type replaced by its expansion: its
 * named type's outer record shape (`recordShape`) at the mapping's
 * modifiers. */
export function settleTerm(term: TypeTerm, records: NamedRecords, where: string,
    refused: (where: string, error: unknown) => Within<{ value: "any"; store: "grow" }, TypeTerm>): Within<{ value: "any"; store: "grow" }, TypeTerm> {
  const go = (t: TypeTerm): TypeTerm => {
    const deferred = deferredOf(t);
    if (!deferred) return mapParts(t, go);
    const object = go(deferred.identity.object);
    const key = go(deferred.key);
    const fail: Fail = message => { throw Error(`${message} in ${where}`); };
    const record: NonNullable<TermScope["record"]> = (reference, failed) => recordShape(reference, records, failed);
    try {
      return expandMapped({ key, value: object, optional: false, readonly: false,
        identity: { ...deferred.identity, object } }, t.span, fail, record);
    } catch (error) {
      return refused(where, error);
    }
  };
  return go(term);
}

/** Whether a document holds a deferred mapped type (`deferredIdentity`):
 * none may reach a serialized document, where it would name no
 * declaration. */
export function deferredIn(value: unknown): Within<{ value: "any"; store: "grow" }, boolean> {
  if (typeof value !== "object" || value === null) return false;
  if (Array.isArray(value)) return value.some(deferredIn);
  if ("module" in value && value.module === DEFERRED_MODULE) return true;
  return Object.values(value).some(deferredIn);
}
