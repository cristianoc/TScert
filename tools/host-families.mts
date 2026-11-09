/** Host families (HOST-FAMILIES.md): the declared type of a family
 * description, the trusted data each host package's contract file
 * contributes, and the one interpreter that reads it: the shape table, the
 * members of each family type and the reading of each declaration under a
 * run's tag selection.
 *
 * The interpreter works on the package's declarations as TypeScript parses
 * them, through `FamilyGraph`, which the declaration reader supplies from
 * the compiler's resolution; the reader then reads each member the reading
 * keeps by its ordinary rules. */
import type { GuardClosure } from "./guard-closure.mts";
import { createHash } from "node:crypto";
import * as ts from "typescript/unstable/ast";
import type { InterfaceDeclaration, TypeElement, TypeNode } from "typescript/unstable/ast";
import type { TypeTerm } from "./declaration-types.mts";
import { emptyFootprint, closedFootprints, footprintEffect, type CallEffect } from "./type-graph.mts";

/** A tag value: a number, or a string for a family whose tag is a string. */
export type TagValue = number | string;
/** The order of tag values: numbers by value, strings by code point, numbers
 * before strings. */
export const compareTags = (a: TagValue, b: TagValue): number =>
  typeof a === "number" ? (typeof b === "number" ? a - b : -1)
    : typeof b === "number" ? 1
    : a < b ? -1 : a > b ? 1 : 0;

/** A rule of the shape table, tried in order for each tag value. */
export type FamilyRule =
  /** The declaration whose tag is the literal `t`, among those not
   * extending another declaration whose tag is `t`. */
  | { rule: "literal" }
  /** The meet of the named generic declarations whose tag parameter's bound
   * admits `t`, each applied at `t`. */
  | { rule: "generic"; declarations: readonly string[] }
  /** The audited shape whose `kind` names `t`, for a tag no declaration
   * states as its literal. */
  | { rule: "audited"; shapes: readonly AuditedShape[] }
  /** A named declaration, its tag read at `t`. */
  | { rule: "base"; declaration: string };

/** A shape the review states for a tag value that no declaration of the
 * family states as its literal (HOST-FAMILIES.md, "The family
 * description"): `kind` names the tag value (its constant); the shape has
 * the members an interface extending `bases` and declaring `members` would
 * have, and is a member of every declaration `bases` reach. Each of
 * `members` is a property the declaration `owner` states, by its text as
 * reviewed, read there; the tag is the tag value. */
export type AuditedShape = {
  kind: string;
  bases: readonly string[];
  members: readonly { owner: string; member: string; text: string }[];
};

/** A member the declarations state required and the runtime leaves absent
 * from the shape of one tag value: read as optional there. `kind` names the
 * tag value (its constant), `owner` the declaration stating the member, and
 * `text` the member's declaration as reviewed. */
export type FamilyCorrection = { kind: string; owner: string; member: string; text: string };
/** A property member the stable-member rule leaves out (HOST-FAMILIES.md,
 * "Stable keys"): its owner, its name and its text as reviewed. */
export type StableExclusion = { owner: string; member: string; text: string };
/** A member whose reads give no one value for a node's life
 * (HOST-FAMILIES.md, "The family contract"): its owner, its name, its text as
 * reviewed, and why: each read builds a fresh value (`allocates`), or the
 * package assigns it on a node it built earlier (`assigned`). No shape states
 * it, so every read of it is of a member the shape does not state. */
export type OmittedMember = { owner: string; member: string; text: string; why: "allocates" | "assigned" };
/** A method whose footprint the family's audit states (HOST-FAMILIES.md,
 * "The family contract"): its owner, its name, its text as reviewed and its
 * kind. An `empty` method's calls change no location of the model, on normal
 * return or throw, and it is read at the empty footprint with `onThrow`. A
 * `callbacks` method's own steps change no location of the model and the
 * only client code it runs is its function-typed arguments', so it is read
 * at each closed footprint, its callbacks' types and its call at that
 * footprint, on normal return. */
export type FootprintMember = { owner: string; member: string; text: string; kind: "empty" | "callbacks" };

/** The reading of a method the family states a footprint for, from its
 * declared type: at the empty footprint with `onThrow` (`empty`); or one
 * signature per closed footprint `ε`, its function-typed parameters and its
 * call at `ε` (`callbacks`), as the array overlay's callback members are
 * (`atEachFootprint`, array-prototype.mts). */
export function footprintReading(kind: FootprintMember["kind"], type: TypeTerm): TypeTerm {
  if (kind === "empty") {
    const effect: CallEffect = footprintEffect(emptyFootprint, { onThrow: true });
    const at = (t: TypeTerm): TypeTerm =>
      t.k === "function" && t.effect.promise === null ? { ...t, effect }
      : t.k === "intersection" ? { ...t, parts: t.parts.map(at) } : t;
    return at(type);
  }
  // A parameter's function type, or each function part of its union with
  // `undefined` (an optional callback), at `effect`.
  const callback = (t: TypeTerm, effect: CallEffect): TypeTerm =>
    t.k === "function" && t.effect.promise === null ? { ...t, effect }
    : t.k === "union" ? { ...t, parts: t.parts.map(p => callback(p, effect)) } : t;
  const each = (s: Extract<TypeTerm, { k: "function" }>): Extract<TypeTerm, { k: "function" }>[] =>
    s.effect.promise !== null ? [s] : closedFootprints.map(footprint => {
      const effect = footprintEffect(footprint);
      return { ...s, effect, params: s.params.map(p => callback(p, effect)),
        rest: s.rest && callback(s.rest, effect) };
    });
  if (type.k === "scheme")
    return { ...type, signatures: type.signatures.flatMap((s): Extract<TypeTerm, { k: "function" | "constructor" }>[] =>
      s.k === "function" ? each(s) : [s]) };
  if (type.k === "function") return { k: "intersection", parts: [...each(type)], span: type.span };
  throw Error("a method read at each callback footprint is a function or a generic method");
}

/** An entry of a guard table (HOST-FAMILIES.md, "The guard table"): the
 * export's name, a node guard or a tag guard, its declared domain, its exact
 * tag set by constant name; the module declaring it, by its path in the
 * package; the helpers its function reads, by `module#name`, and its
 * dependency edges; and its function's text as reviewed. */
export type GuardEntry = {
  name: string;
  kind: "node" | "tag";
  domain: string;
  tags: readonly string[];
  /** What the guard does on `undefined`, outside its domain
   * (HOST-FAMILIES.md, "Undefined arguments"): throws a `TypeError` before
   * any other step, returns `false` having run nothing else, or is
   * `unadmitted`, an argument the domain obligation refuses. */
  onUndefined: GuardUndefined;
  module: string;
  helpers: readonly string[];
  /** Each binding the closure imports: the importing module, the local
   * name, the module it resolves to and the name that module exports. */
  edges: readonly (readonly [string, string, string, string])[];
  text: string;
};
/** A guard's audited behaviour on `undefined` (HOST-FAMILIES.md, "Undefined
 * arguments"). */
export type GuardUndefined = "unadmitted" | "throws" | "false";
/** A family's guard table: the entry point and the resolution conditions
 * its entries were resolved under, the entry point's module and complete
 * executable closure (file digests and static edges), each helper with
 * its text (no helper twice), the entries, and
 * the guards the package declares that the recognition contract excludes,
 * each with its reason. */
export type GuardTable = {
  entryPoint: string;
  conditions: readonly string[];
  entryModule: string;
  closure: GuardClosure;
  helpers: readonly (readonly [string, string])[];
  guards: readonly GuardEntry[];
  excluded: readonly (readonly [string, string])[];
};

/** A family description (HOST-FAMILIES.md, "The family description"). */
export type FamilyDescription = {
  /** The host package, whose audited files hold every declaration below:
   * the name and version its manifest states. */
  package: { readonly name: string; readonly version: string };
  /** The audited installation (C0): the package of that name as Node's
   * package resolution finds it from the directory `from`, relative to the
   * repository's root, and the digest of its declarations
   * (`declarationsDigest` in `family-activation.mts`). */
  installation: { readonly from: string; readonly digest: string };
  /** The value `m_F` of the model's `[[host]]` in every member. */
  marker: string;
  /** The root declaration, an inheritance root: the family's declarations
   * are the interfaces reaching it through `extends`. */
  root: { name: string; form: "inheritance"; text: string };
  /** The tag field, its primitive, and the enum holding its constants. */
  tag: { field: string; primitive: "number" | "string"; constants: { enum: string } };
  table: readonly FamilyRule[];
  corrections: readonly FamilyCorrection[];
  /** The members whose reads give no one value for a node's life, each
   * omitted from every shape. */
  omitted: readonly OmittedMember[];
  /** The methods whose footprint the family's audit states. */
  footprints: readonly FootprintMember[];
  /** The stable-member rule: every property member of a shape, required or
   * optional, the tag and the corrected members included, is stable but
   * these. */
  stable: { excluded: readonly StableExclusion[] };
  /** The guard table: the guards read from an audited entry, every other
   * guard of the family read without predicate. */
  guards: GuardTable;
  /** The guard kinds whose audited behaviour on `undefined` the review
   * admits (HOST-FAMILIES.md, "Undefined arguments"): an entry of another
   * kind is `unadmitted` there. */
  undefinedInputs: readonly GuardEntry["kind"][];
};

/** The package's declarations as the interpreter reads them, resolved by
 * the compiler. */
export type FamilyGraph = {
  /** Every interface of the family: the root and those reaching it. */
  interfaces: readonly InterfaceDeclaration[];
  /** A declaration's resolved bases, in the order its heritage states them;
   * each may be outside the family (`Node`'s `ReadonlyTextRange`). */
  bases: (declaration: InterfaceDeclaration) => readonly InterfaceDeclaration[];
  /** The tag values a type states: the literal constants of a set, through
   * aliases and unions; null for a type that is no set of literals (the
   * enum itself, `number`, a type parameter). */
  literals: (type: TypeNode) => readonly TagValue[] | null;
  /** The tag's constants: the enum's values, each once, ascending. */
  values: readonly TagValue[];
  /** A tag value's constant name, the first the enum states for it. */
  constantName: (value: TagValue) => Modifies<{}, string>;
  /** The name of a declaration's tag parameter, or null. */
  tagParameter: (declaration: InterfaceDeclaration) => string | null;
  /** Whether a member is declared optional, `name?: T`. */
  questioned: (member: TypeElement, ...further: unknown[]) => boolean;
  /** A member's name, where it is an identifier. */
  name: (member: TypeElement) => string | null;
  /** The text of a member as reviewed against (`getText`, trimmed). */
  text: (member: TypeElement) => string;
  /** Whether a member's type mentions the named type parameter. */
  mentions: (member: TypeElement, parameter: string) => boolean;
  fail: (message: string) => never;
};

/** One member of a flattened declaration: its name, the declaration
 * stating it, and its signatures there (a method may have several). */
export type FlatMember = { readonly name: string; readonly owner: InterfaceDeclaration; readonly members: readonly TypeElement[] };

/** Where a tag value's shape comes from. */
export type ShapeSource =
  | { rule: "literal"; declaration: InterfaceDeclaration }
  | { rule: "generic"; declarations: readonly InterfaceDeclaration[] }
  /** An audited shape: its resolved bases and its flattened members. */
  | { rule: "audited"; shape: AuditedShape; bases: readonly InterfaceDeclaration[]; members: readonly FlatMember[] }
  | { rule: "base"; declaration: InterfaceDeclaration };

/** How a declaration of the family is read. */
export type FamilyTag =
  /** Its tag is a set of literals: read as its flattened declared members,
   * the shape itself where it is the table's choice, a refinement
   * otherwise. */
  | { k: "literal"; values: readonly TagValue[] }
  /** Its tag is its own type parameter: a generic shape, applied at tags. */
  | { k: "parameter"; parameter: string }
  /** Its tag is no set of literals: the union of its members' shapes. */
  | { k: "open" };

/** An arm of a family type's reading under a selection. */
export type FamilyArm =
  /** The table's literal declaration for a tag value. */
  | { k: "declaration"; declaration: InterfaceDeclaration }
  /** The meet of generic declarations, each applied at the tag set (one
   * value, or several merged where only the tag varies). */
  | { k: "generic"; declarations: readonly InterfaceDeclaration[]; values: readonly TagValue[] }
  /** A synthetic shape: a base declaration read at a tag set, or the
   * residual joining the shapes the selection leaves out. */
  | { k: "synthetic"; name: string; values: readonly TagValue[]; fields: readonly SyntheticField[] };

/** A member of a synthetic shape: its name, the flattened members it joins
 * (one per distinct declaration), each with the tag value it is read at
 * where its owner is generic, and whether it is optional. The tag member is
 * left out: a synthetic shape's tag is its tag set. */
export type SyntheticField = { name: string; sources: readonly { member: FlatMember; value: TagValue }[]; optional: boolean };

/** The interpreter's reading of one family. */
export type FamilyTable = {
  readonly description: FamilyDescription;
  readonly tagOf: (declaration: InterfaceDeclaration) => FamilyTag;
  /** A declaration's members, its bases' included, the nearest declaration
   * of each name, without the members whose read allocates. */
  readonly flatten: (declaration: InterfaceDeclaration) => readonly FlatMember[];
  /** Whether a flattened member is optional in a reading covering the tag
   * values `values`: so declared, or corrected at one of them. */
  readonly optional: (member: FlatMember, values: readonly TagValue[]) => boolean;
  /** Whether the stable-member rule names a flattened property member:
   * every one the description does not exclude. A shape states it stable
   * where it is required there. */
  readonly stable: (member: FlatMember) => boolean;
  /** Whether a synthetic shape over these tag values states its tag stable:
   * where every source shape's tag member is. */
  readonly tagStable: (values: readonly TagValue[]) => boolean;
  /** The tag values a declaration's values can have: its literals, its tag
   * parameter's bound, or the members of an open declaration. */
  readonly tagsOf: (declaration: InterfaceDeclaration) => readonly TagValue[];
  /** The family's shape sources, by tag value. */
  readonly shapes: ReadonlyMap<TagValue, ShapeSource>;
  /** A shape source's flattened members: each generic declaration's, the
   * declaration's, or the audited shape's. */
  readonly sourceMembers: (source: ShapeSource) => readonly FlatMember[];
  /** `members_F(A)`: the tag values whose shape source reaches `A`. */
  readonly membersOf: (declaration: InterfaceDeclaration) => readonly TagValue[];
  /** The arms of an open declaration's reading under a selection, in tag
   * order, the residual last. */
  readonly arms: (declaration: InterfaceDeclaration, selection: ReadonlySet<TagValue>) => readonly FamilyArm[];
};

/** The interpreter: the table and membership on the declaration graph as
 * declared, before any flattening or correction. */
export function familyTable(description: FamilyDescription, graph: FamilyGraph): FamilyTable {
  const family = new Set(graph.interfaces);
  const byName = new Map(graph.interfaces.map(d => [d.name.text, d]));
  const named = (name: string): InterfaceDeclaration =>
    byName.get(name) ?? graph.fail(`the family ${description.marker} has no declaration ${name}`);
  // `a` reaches `b` through `extends`, itself included.
  const reachCache = new Map<InterfaceDeclaration, Set<InterfaceDeclaration>>();
  const reached = (a: InterfaceDeclaration): Set<InterfaceDeclaration> => {
    const known = reachCache.get(a);
    if (known) return known;
    const set = new Set<InterfaceDeclaration>([a]);
    reachCache.set(a, set);
    for (const b of graph.bases(a)) for (const x of reached(b)) set.add(x);
    return set;
  };
  const reaches = (a: InterfaceDeclaration, b: InterfaceDeclaration): boolean => reached(a).has(b);

  // Flattening: the nearest declaration of each name. A name two bases
  // state through different declarations, neither below the other, is
  // refused: its contract would be their meet, which no rule here forms.
  const omitted = new Set(description.omitted.map(x => `${x.owner}.${x.member}`));
  const flatCache = new Map<InterfaceDeclaration, FlatMember[]>();
  const flatten = (d: InterfaceDeclaration): FlatMember[] => {
    const known = flatCache.get(d);
    if (known) return known;
    const own: { name: string; owner: InterfaceDeclaration; members: TypeElement[] }[] = [];
    for (const m of d.members) {
      const name = graph.name(m) ?? graph.fail(`${d.name.text} has a member without a plain name: ${graph.text(m)}`);
      const existing = own.find(f => f.name === name);
      if (existing) existing.members.push(m);
      else own.push({ name, owner: d, members: [m] });
    }
    const result = combine(d.name.text, own, graph.bases(d));
    flatCache.set(d, result);
    return result;
  };
  // The members of a declaration named `name` stating `own` and extending
  // `bases`: its own, but the omitted ones, and each other name's nearest.
  function combine(name: string, own: readonly FlatMember[], bases: readonly InterfaceDeclaration[]): FlatMember[] {
    const result = own.filter(f => !omitted.has(`${f.owner.name.text}.${f.name}`));
    const names = new Set(own.map(f => f.name));
    const inherited = new Map<string, FlatMember[]>();
    for (const b of bases)
      for (const f of flatten(b)) {
        if (names.has(f.name)) continue;
        const list = inherited.get(f.name) ?? [];
        if (!list.some(g => g.owner === f.owner)) list.push(f);
        inherited.set(f.name, list);
      }
    for (const [member, list] of inherited) {
      const nearest = list.filter(f => !list.some(g => g !== f && reaches(g.owner, f.owner)));
      const [only] = nearest;
      if (!only || nearest.length !== 1)
        graph.fail(`${name} inherits ${member} from ${nearest.map(f => f.owner.name.text).join(" and ")}, neither extending the other`);
      result.push(only);
    }
    return result;
  }
  // The audited shapes, each checked against the declarations it was
  // reviewed at: its tag a constant no declaration states as its literal,
  // its bases declarations of the family, each member a property its owner
  // states as reviewed, omitted nowhere.
  const audited = new Map<TagValue, Extract<ShapeSource, { rule: "audited" }>>();
  for (const rule of description.table) {
    if (rule.rule !== "audited") continue;
    for (const shape of rule.shapes) {
      const value = graph.values.find(t => graph.constantName(t) === shape.kind);
      if (value === undefined) graph.fail(`the audited shape ${shape.kind} names no tag`);
      if (audited.has(value)) graph.fail(`the tag ${shape.kind} has two audited shapes`);
      const own: FlatMember[] = [];
      for (const m of shape.members) {
        const owner = named(m.owner);
        const members = owner.members.filter(x => graph.name(x) === m.member);
        const [only] = members;
        if (!only || members.length !== 1 || graph.text(only) !== m.text || !("type" in only))
          graph.fail(`the audited shape ${shape.kind} states ${m.owner}.${m.member}, which is not declared as reviewed: ${m.text}`);
        if (m.member === description.tag.field || omitted.has(`${m.owner}.${m.member}`))
          graph.fail(`the audited shape ${shape.kind} states ${m.owner}.${m.member}, the tag or an omitted member`);
        if (shape.members.filter(x => x.member === m.member).length !== 1)
          graph.fail(`the audited shape ${shape.kind} states ${m.member} twice`);
        own.push({ name: m.member, owner, members: [only] });
      }
      const bases: InterfaceDeclaration[] = [];
      for (const b of shape.bases) bases.push(named(b));
      audited.set(value, { rule: "audited", shape, bases, members: combine(shape.kind, own, bases) });
    }
  }
  const tagMember = (d: InterfaceDeclaration): FlatMember | undefined =>
    flatten(d).find(f => f.name === description.tag.field);
  const tagOf = (d: InterfaceDeclaration): FamilyTag => {
    const member = tagMember(d);
    const [signature] = member?.members ?? [];
    const type = signature && ts.isPropertySignatureDeclaration(signature) ? signature.type : undefined;
    if (!member || !type || member.members.length !== 1)
      return graph.fail(`${d.name.text} states no ${description.tag.field} of one type`);
    const parameter = member.owner === d ? graph.tagParameter(d) : null;
    if (parameter !== null) return { k: "parameter", parameter };
    const values = graph.literals(type);
    return values ? { k: "literal", values } : { k: "open" };
  };

  // The table, rule by rule for each tag value.
  const candidates = new Map<TagValue, InterfaceDeclaration[]>();
  for (const d of graph.interfaces) {
    const tag = tagOf(d);
    if (tag.k !== "literal" || tag.values.length !== 1) continue;
    const [t] = tag.values;
    if (t === undefined) continue;
    candidates.set(t, [...(candidates.get(t) ?? []), d]);
  }
  const shapes = new Map<TagValue, ShapeSource>();
  for (const t of audited.keys())
    if (candidates.get(t)?.length)
      graph.fail(`the tag ${graph.constantName(t)} has an audited shape and a literal declaration`);
  for (const t of graph.values) {
    for (const rule of description.table) {
      if (rule.rule === "audited") {
        const source = audited.get(t);
        if (!source) continue;
        shapes.set(t, source);
        break;
      }
      if (rule.rule === "literal") {
        const list = candidates.get(t) ?? [];
        const chosen = list.filter(d => !list.some(o => o !== d && reaches(d, o)));
        if (!list.length) continue;
        const [only] = chosen;
        if (!only || chosen.length !== 1)
          graph.fail(`the tag ${graph.constantName(t)} has ${chosen.length} literal declarations`);
        shapes.set(t, { rule: "literal", declaration: only });
        break;
      }
      if (rule.rule === "generic") {
        const declarations = rule.declarations.map(named).filter(g => {
          const tag = tagOf(g);
          if (tag.k !== "parameter") graph.fail(`${g.name.text} has no tag parameter`);
          // The reading applies a generic shape at its tag as its one argument.
          if ((g.typeParameters ?? []).length !== 1)
            graph.fail(`${g.name.text} has parameters beside its tag parameter, which the table reads as its only one`);
          const parameter = g.typeParameters?.find(p => p.name.text === tag.parameter);
          const bound = parameter?.constraint ? graph.literals(parameter.constraint) : null;
          if (!bound) return graph.fail(`${g.name.text}'s tag parameter has no bound of literals`);
          return bound.includes(t);
        });
        if (!declarations.length) continue;
        shapes.set(t, { rule: "generic", declarations });
        break;
      }
      shapes.set(t, { rule: "base", declaration: named(rule.declaration) });
      break;
    }
    if (!shapes.has(t)) graph.fail(`the table selects no shape for the tag ${graph.constantName(t)}`);
  }
  const sourceReaches = (source: ShapeSource, a: InterfaceDeclaration): boolean =>
    source.rule === "generic" ? source.declarations.some(g => reaches(g, a))
    : source.rule === "audited" ? source.bases.some(b => reaches(b, a)) : reaches(source.declaration, a);
  const membersCache = new Map<InterfaceDeclaration, TagValue[]>();
  const membersOf = (a: InterfaceDeclaration): TagValue[] => {
    const known = membersCache.get(a);
    if (known) return known;
    const result = graph.values.filter(t => {
      const source = shapes.get(t);
      return !!source && sourceReaches(source, a);
    });
    membersCache.set(a, result);
    return result;
  };

  // Corrections, each checked against the declaration it was reviewed at.
  const corrected = new Set<string>();
  for (const c of description.corrections) {
    const owner = named(c.owner);
    const members = owner.members.filter(m => graph.name(m) === c.member);
    const [only] = members;
    if (!only || members.length !== 1 || graph.text(only) !== c.text)
      graph.fail(`${c.owner}.${c.member} is not declared as reviewed: ${c.text}`);
    const value = graph.values.find(t => graph.constantName(t) === c.kind);
    if (value === undefined) graph.fail(`the correction of ${c.owner}.${c.member} names no tag ${c.kind}`);
    corrected.add(`${value}:${c.owner}.${c.member}`);
  }
  // The members whose read allocates, each checked against the declaration
  // it was reviewed at.
  for (const x of description.omitted) {
    const owner = named(x.owner);
    const members = owner.members.filter(m => graph.name(m) === x.member);
    const [only] = members;
    if (!only || members.length !== 1 || graph.text(only) !== x.text)
      graph.fail(`the omitted member ${x.owner}.${x.member} is not declared as reviewed: ${x.text}`);
  }
  // The methods whose footprint the family states, each checked against the
  // declaration it was reviewed at.
  for (const x of description.footprints) {
    const owner = named(x.owner);
    const members = owner.members.filter(m => graph.name(m) === x.member);
    const [only] = members;
    if (!only || members.length !== 1 || graph.text(only) !== x.text)
      graph.fail(`the method ${x.owner}.${x.member} whose footprint the family states is not declared as reviewed: ${x.text}`);
  }
  // The stable-member rule's exclusions, each checked against the
  // declaration it was reviewed at: a property member that declaration
  // states.
  const unstable = new Set<string>();
  for (const x of description.stable.excluded) {
    const owner = named(x.owner);
    const members = owner.members.filter(m => graph.name(m) === x.member);
    const [only] = members;
    if (!only || members.length !== 1 || graph.text(only) !== x.text)
      graph.fail(`the stable-member rule excludes ${x.owner}.${x.member}, which is not declared as reviewed: ${x.text}`);
    unstable.add(`${x.owner}.${x.member}`);
  }
  const stable = (f: FlatMember): boolean => !unstable.has(`${f.owner.name.text}.${f.name}`);
  // The tag of a synthetic shape over `values` is stable where every source
  // shape's tag member is.
  const tagStable = (values: readonly TagValue[]): boolean => values.every(t => {
    const source = shapes.get(t);
    const tags = source ? sourceMembers(source).filter(f => f.name === description.tag.field) : [];
    return tags.length > 0 && tags.every(stable);
  });
  const optional = (f: FlatMember, values: readonly TagValue[]): boolean =>
    f.members.some(graph.questioned) || values.some(v => corrected.has(`${v}:${f.owner.name.text}.${f.name}`));
  const tagsOf = (d: InterfaceDeclaration): readonly TagValue[] => {
    const tag = tagOf(d);
    if (tag.k === "literal") return tag.values;
    if (tag.k === "open") return membersOf(d);
    const parameter = d.typeParameters?.find(p => p.name.text === tag.parameter);
    return (parameter?.constraint ? graph.literals(parameter.constraint) : null)
      ?? graph.fail(`${d.name.text}'s tag parameter has no bound of literals`);
  };
  // Whether a shape source's other members depend on its tag parameter: then
  // its applications at different tags are different arms.
  const tagOnly = (g: InterfaceDeclaration): boolean => {
    const tag = tagOf(g);
    return tag.k === "parameter" && flatten(g).every(f => f.name === description.tag.field ||
      f.members.every(m => !graph.mentions(m, tag.parameter)));
  };

  // A synthetic shape's members: those every source has, each joining the
  // distinct declarations of it, optional where one is.
  const sourceMembers = (source: ShapeSource): readonly FlatMember[] =>
    source.rule === "generic" ? source.declarations.flatMap(d => flatten(d))
    : source.rule === "audited" ? source.members : flatten(source.declaration);
  const synthetic = (base: string, values: readonly TagValue[]): FamilyArm => {
    const per: { t: TagValue; members: readonly FlatMember[] }[] = [];
    for (const t of values) {
      const source = shapes.get(t);
      per.push(source ? { t, members: sourceMembers(source) } : graph.fail(`no shape for ${t}`));
    }
    const [first] = per;
    const fields: SyntheticField[] = [];
    for (const f of first?.members ?? []) {
      if (f.name === description.tag.field || fields.some(x => x.name === f.name)) continue;
      const found = per.map(p => ({ t: p.t, members: p.members.filter(g => g.name === f.name) }));
      if (found.some(p => !p.members.length)) continue;
      const sources: { member: FlatMember; value: TagValue }[] = [];
      for (const p of found)
        for (const member of p.members)
          if (!sources.some(s => s.member.owner === member.owner &&
              (!family.has(member.owner) || tagOf(member.owner).k !== "parameter" || s.value === p.t)))
            sources.push({ member, value: p.t });
      fields.push({ name: f.name, sources, optional: found.some(p => p.members.some(g => optional(g, [p.t]))) });
    }
    const digest = createHash("sha256").update(values.join(",")).digest("hex").slice(0, 16);
    return { k: "synthetic", name: `${base} at ${values.length} tags ${digest}`, values, fields };
  };
  const arms = (a: InterfaceDeclaration, selection: ReadonlySet<TagValue>): FamilyArm[] => {
    const members = membersOf(a);
    // Each arm at the least tag it holds, the arms in tag order: a literal
    // declaration's tag, a generic application's or a base shape's first.
    const groups = new Map<string, { first: TagValue; arm: () => FamilyArm; values: TagValue[] }>();
    for (const t of members) {
      if (!selection.has(t)) continue;
      const source = shapes.get(t);
      if (!source) continue;
      if (source.rule === "literal") {
        const declaration = source.declaration;
        groups.set(`literal@${t}`, { first: t, values: [t], arm: () => ({ k: "declaration", declaration }) });
        continue;
      }
      if (source.rule === "audited") {
        groups.set(`audited@${t}`, { first: t, values: [t], arm: () => synthetic(source.shape.kind, [t]) });
        continue;
      }
      const key = source.rule === "generic"
        ? source.declarations.map(g => g.name.text).join("&") + (source.declarations.every(tagOnly) ? "" : `@${t}`)
        : `base:${source.declaration.name.text}`;
      const known = groups.get(key);
      if (known) { known.values.push(t); continue; }
      const values = [t];
      groups.set(key, { first: t, values, arm: source.rule === "generic"
        ? () => ({ k: "generic", declarations: source.declarations, values })
        : () => synthetic(source.declaration.name.text, values) });
    }
    const result: FamilyArm[] = [];
    for (const g of [...groups.values()].sort((x, y) => compareTags(x.first, y.first))) result.push(g.arm());
    const rest = members.filter(t => !selection.has(t));
    if (rest.length) result.push(synthetic(`${a.name.text} residual`, rest));
    return result;
  };
  for (const d of graph.interfaces) if (!family.has(d)) graph.fail("a family interface outside the family");
  return { description, tagOf, flatten, optional, stable, tagStable, tagsOf, shapes, sourceMembers, membersOf, arms };
}
