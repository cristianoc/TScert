/** A named type's outer record shape, which a mapped type whose value is
 * `X[P]` maps at a named X (SOURCE-CONTRACTS.md, "Library types", the rule
 * mapped-identity), and the settling of mapped types read before the
 * definitions they reach were complete. Both readers use it: the
 * declaration graph once its collection ends, and the gate for the file's
 * annotations, read after the declaration document is complete. */
import type { CallEffect, CallPromise, DeclarationDocument, ElementKinds, DeclarationIdentity, PropertyKey, TypeDefinition, TypeTerm, ValueRoot, WrittenApplication } from "./declaration-types.mts";
import type { Ast, ModuleAst } from "./fragment.mts";
import type { Span } from "./span.mts";
import { astHolds, documentHolds, moduleHolds } from "./fragment-parts.mts";
import { DEFERRED_MODULE, deferredOf, expandMapped, mapTypeParts, substitute, type AliasHook, type RecordHook } from "./type-term.mts";

type Reference = Extract<TypeTerm, { k: "reference" }>;
type ObjectTerm = Extract<TypeTerm, { k: "object" }>;
type Index = { readonly: boolean; value: TypeTerm; span: Span };
type Fail = (message: string) => never;

/** A definition's key: its full declaration identity. */
export const definitionKey = (id: DeclarationIdentity): Within<{ value: "keep"; store: "keep" }, string> =>
  JSON.stringify([id.module, id.span, id.name]);

/** The complete definitions a shape is read from: each by its identity,
 * and whether it is a record, an interface or a type alias read as its
 * declared body outside a host type, or an alias of a named type
 * (`records` of the declaration graph);
 * a class, a host type, a library interface read through its overlay or a
 * definition the reader states itself is none. */
// Classification preserves the definition being inspected; definition lookup
// can settle and cache definitions under its separate growth contract.
export type NamedRecords = {
  definition(id: DeclarationIdentity, fail: Fail): Within<{ value: "any"; store: "grow" }, TypeDefinition | undefined>;
  record(id: DeclarationIdentity): Within<{ value: "keep"; store: "keep" }, boolean>;
};

const PREFIX = "a mapped type's value names its key, over a named type";

/** A term's data as text, its spans aside: equal texts are the same type.
 * A declaration identity's span is the declaration's and is written; any
 * other span, and a reference's argument spans, only locate the term. The
 * text is JSON, each kind's fields in the order `TypeTerm` declares them, an
 * absent optional field left out: a kind added to `TypeTerm` fails the
 * compilation of the `switch`, and a field added to a kind is written only
 * once `termText` names it. */
export function termText(t: TypeTerm): Within<{ value: "keep"; store: "keep" }, string> {
  const k = `{"k":${JSON.stringify(t.k)}`;
  switch (t.k) {
    case "atom": return `${k},"name":${JSON.stringify(t.name)}}`;
    case "literal": return `${k},"name":${JSON.stringify(t.name)},"text":${JSON.stringify(t.text)}}`;
    case "unique": return `${k},"symbol":${JSON.stringify(t.symbol)}}`;
    case "union":
    case "intersection": return `${k},"parts":${termsText(t.parts)}}`;
    case "array":
      return `${k},"presence":${JSON.stringify(t.presence)},"readonly":${JSON.stringify(t.readonly)},"element":${termText(t.element)}}`;
    case "tuple":
      return `${k},"presence":${JSON.stringify(t.presence)},"readonly":${JSON.stringify(t.readonly)},` +
        `"required":${termsText(t.required)},"optional":${termsText(t.optional)},"rest":${optionalTermText(t.rest)}}`;
    case "object":
      return `${k},"fields":[${t.fields.map(fieldText).join(",")}],` +
        `"stringIndex":${t.stringIndex === null ? "null" : indexText(t.stringIndex)}` +
        (t.numberIndex ? `,"numberIndex":${indexText(t.numberIndex)}` : "") +
        (t.symbolIndex ? `,"symbolIndex":${indexText(t.symbolIndex)}` : "") +
        `,"calls":${termsText(t.calls)}` +
        (t.prototype ? `,"prototype":${termText(t.prototype)}` : "") +
        (t.host !== undefined ? `,"host":${JSON.stringify(t.host)}` : "") +
        (t.stable ? `,"stable":[${t.stable.map(s => JSON.stringify(s)).join(",")}]` : "") + "}";
    case "function":
      return `${k},"effect":${effectText(t.effect)},"receiver":${optionalTermText(t.receiver)},` +
        `"params":${termsText(t.params)},"rest":${optionalTermText(t.rest)},"result":${termText(t.result)}}`;
    case "constructor":
      return `${k},"effect":${effectText(t.effect)},"params":${termsText(t.params)},"rest":${optionalTermText(t.rest)},` +
        `"result":${termText(t.result)}` +
        (t.statics ? `,"statics":[${t.statics.map(staticText).join(",")}]` : "") + "}";
    case "pack": return `${k},"of":${termText(t.of)}}`;
    case "scheme": return `${k},"binders":[${t.binders.map(binderText).join(",")}],"signatures":${termsText(t.signatures)}}`;
    case "callable":
    case "self": return `${k}}`;
    case "parameter": return `${k},"index":${JSON.stringify(t.index)}}`;
    case "binder": return `${k},"name":${JSON.stringify(t.name)}}`;
    case "reference":
      return `${k},"reference":{"name":${JSON.stringify(t.reference.name)},"target":${identityText(t.reference.target)}},` +
        `"args":${termsText(t.args)}}`;
  }
}

/** A list of terms as text, each by `termText`. */
export function termsText(ts: readonly TypeTerm[]): Within<{ value: "keep"; store: "keep" }, string> {
  return `[${ts.map(termText).join(",")}]`;
}

/** A declaration identity as text, its span included. */
export function identityText(id: DeclarationIdentity): Within<{ value: "keep"; store: "keep" }, string> {
  return `{"module":${JSON.stringify(id.module)},"name":${JSON.stringify(id.name)},"span":[${JSON.stringify(id.span[0])},${JSON.stringify(id.span[1])}]}`;
}

function optionalTermText(t: TypeTerm | null): Within<{ value: "keep"; store: "keep" }, string> {
  return t === null ? "null" : termText(t);
}

function propertyKeyText(name: PropertyKey): Within<{ value: "keep"; store: "keep" }, string> {
  return typeof name === "string" ? JSON.stringify(name) : `{"symbol":${JSON.stringify(name.symbol)}}`;
}

/** An object type's field as text, its span aside. */
function fieldText(f: ObjectTerm["fields"][number]): Within<{ value: "keep"; store: "keep" }, string> {
  return `{"name":${propertyKeyText(f.name)},"optional":${JSON.stringify(f.optional)},"readonly":${JSON.stringify(f.readonly)},"type":${termText(f.type)}}`;
}

/** An index signature as text, its span aside. */
function indexText(i: Index): Within<{ value: "keep"; store: "keep" }, string> {
  return `{"readonly":${JSON.stringify(i.readonly)},"value":${termText(i.value)}}`;
}

function staticText(s: { name: PropertyKey; type: TypeTerm; readonly?: true }): Within<{ value: "keep"; store: "keep" }, string> {
  return `{"name":${propertyKeyText(s.name)},"type":${termText(s.type)}${s.readonly ? `,"readonly":true` : ""}}`;
}

function binderText(b: Extract<TypeTerm, { k: "scheme" }>["binders"][number]): Within<{ value: "keep"; store: "keep" }, string> {
  const resolution = b.resolution === null ? "null"
    : `{"observation":${JSON.stringify(b.resolution.observation)},"result":${b.resolution.result === null ? "null" : JSON.stringify(b.resolution.result)}}`;
  return `{"name":${JSON.stringify(b.name)},"bound":${optionalTermText(b.bound)},"resolution":${resolution},"default":${optionalTermText(b.default)}}`;
}

/** A call promise's JSON text, built from its one key and its parameter. */
function promiseText(p: CallPromise): Within<{ value: "keep"; store: "keep" }, string> {
  return p.guards !== undefined ? `{"guards":{"param":${JSON.stringify(p.guards.param)}}}`
    : `{"asserts":{"param":${JSON.stringify(p.asserts.param)}}}`;
}

/** A call effect as text; its promise by its JSON text. */
function effectText(e: CallEffect): Within<{ value: "keep"; store: "keep" }, string> {
  return `{"footprint":{"value":${JSON.stringify(e.footprint.value)},"store":${JSON.stringify(e.footprint.store)}},` +
    `"promise":${e.promise === null ? "null" : promiseText(e.promise)},"fresh":${JSON.stringify(e.fresh)},` +
    `"receiverStore":${JSON.stringify(e.receiverStore)},"onThrow":${JSON.stringify(e.onThrow)},` +
    `"receiverOwn":${JSON.stringify(e.receiverOwn)},"freshObject":${JSON.stringify(e.freshObject)},` +
    `"requires":${kindsText(e.requires)},"elements":${kindsText(e.elements)},"pre":${JSON.stringify(e.pre)}}`;
}

/** An elements predicate as text: `null` or its kinds' list. */
function kindsText(kinds: ElementKinds | null): Within<{ value: "keep"; store: "keep" }, string> {
  return kinds === null ? "null" : `[${kinds.map(k => JSON.stringify(k)).join(",")}]`;
}

const keyText = (name: PropertyKey): Within<{ value: "any"; store: "grow" }, string> =>
  typeof name === "string" ? name : `[symbol ${name.symbol}]`;

/** What `reference` denotes (`AliasHook`, type-term.mts): `"record"` for a
 * record written as one whose equation is a record (an interface, an alias
 * of a record literal), its definition's equation at the reference's
 * arguments for any other definition that has one, an alias of a named
 * type included, which the caller follows in turn; refused otherwise. */
export function aliasMeaning(reference: Reference, records: NamedRecords, fail: Fail): Within<{ value: "any"; store: "grow" }, TypeTerm | "record"> {
  const target = reference.reference.target;
  const name = `${target.module}#${target.name}`;
  const definition = records.definition(target, fail) ?? fail(`a type with no definition the reader holds: ${name}`);
  if (definition.parameters.length !== reference.args.length)
    return fail(`a type applied at ${reference.args.length} of its ${definition.parameters.length} parameters: ${name}`);
  if (!definition.expression) return fail(`a type with no equation the reader holds: ${name}`);
  if (records.record(target) && definition.expression.k === "object") return "record";
  return substitute(definition.expression, reference.args);
}

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
      else if (fieldText(declared) !== fieldText(field))
        fail(`${PREFIX} that redeclares its base's member ${keyText(field.name)} at another type or modifier: ${name}`);
    }
    const index = (mine: Index | null | undefined, theirs: Index | null | undefined, what: string): Index | null => {
      if (!theirs) return mine ?? null;
      if (!mine) return theirs;
      if (indexText(mine) !== indexText(theirs)) fail(`${PREFIX} that redeclares its base's ${what} index at another type or modifier: ${name}`);
      return mine;
    };
    const numberIndex = index(own.numberIndex, base.numberIndex, "number");
    const symbolIndex = index(own.symbolIndex, base.symbolIndex, "symbol");
    return { ...own, fields, stringIndex: index(own.stringIndex, base.stringIndex, "string"),
      ...(numberIndex ? { numberIndex } : {}), ...(symbolIndex ? { symbolIndex } : {}) };
  };
  return named(reference, []);
}

/** Every deferred mapped type of a declaration document's definitions,
 * values and applications replaced by its expansion at the complete
 * definitions (`settleTerm`): each definition settled once, before a
 * shape is read from it, so a definition whose settling needs its own shape
 * is refused. The refusal callback throws with the source location. */
export function settleDocument(document: { definitions: TypeDefinition[]; values: ValueRoot[]; applications: WrittenApplication[] },
    record: (id: DeclarationIdentity) => Within<{ value: "keep"; store: "keep" }, boolean>,
    refused: (where: string, error: unknown) => never): Within<{ value: "any"; store: "grow" }, { definitions: TypeDefinition[]; values: ValueRoot[]; applications: WrittenApplication[] }> {
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
    refused: (where: string, error: unknown) => never): Within<{ value: "any"; store: "grow" }, TypeTerm> {
  const go = (t: TypeTerm): TypeTerm => {
    const deferred = deferredOf(t);
    if (!deferred) return mapTypeParts(t, go);
    const object = go(deferred.identity.object);
    const key = go(deferred.key);
    const fail: Fail = message => { throw Error(`${message} in ${where}`); };
    const record: RecordHook = (reference, failed) => recordShape(reference, records, failed);
    const alias: AliasHook = (reference, failed) => aliasMeaning(reference, records, failed);
    try {
      return expandMapped({ key, value: object, optional: false, readonly: false,
        identity: { ...deferred.identity, object } }, t.span, fail, record, alias);
    } catch (error) {
      return refused(where, error);
    }
  };
  return go(term);
}

/* Whether a document holds a deferred mapped type (`deferredIdentity`):
 * none may reach a serialized document, where it would name no
 * declaration. A declaration of its module is one, wherever it is named. */
const deferredTerm = (t: TypeTerm): Within<{ value: "any"; store: "grow" }, boolean> =>
  t.k === "reference" && t.reference.target.module === DEFERRED_MODULE;
const deferredDeclaration = (id: DeclarationIdentity): Within<{ value: "any"; store: "grow" }, boolean> =>
  id.module === DEFERRED_MODULE;

/** Whether a declaration document holds a deferred mapped type. */
export function deferredInDocument(doc: DeclarationDocument): Within<{ value: "any"; store: "grow" }, boolean> {
  return documentHolds(doc, deferredTerm, deferredDeclaration);
}

/** Whether a lowered file, its documents and code, holds a deferred mapped
 * type. */
export function deferredInAst(ast: Ast): Within<{ value: "any"; store: "grow" }, boolean> {
  return astHolds(ast, deferredTerm, deferredDeclaration);
}

/** Whether an imported module's entry, its documents and code, holds a
 * deferred mapped type. */
export function deferredInModule(module: ModuleAst): Within<{ value: "any"; store: "grow" }, boolean> {
  return moduleHolds(module, deferredTerm, deferredDeclaration);
}
