/** The one reading of TypeScript type syntax as a source type term. Function
 * annotations and declaration bodies share it: what differs between them is
 * where a name resolves, which the caller's scope decides, and which record
 * forms an annotation may state. */
import * as ts from "typescript/unstable/ast";
import type { Identifier, Node, SourceFile, TypeAliasDeclaration, TypeElement, TypeNode, TypeReferenceNode } from "typescript/unstable/ast";
import type { Span } from "./span.mts";
import { childrenOf, isTypeAlias } from "./syntax.mts";
import type { ClosedFootprint, PropertyKey, ResolutionSlots, StatedEffect, TypeTerm } from "./declaration-types.mts";
import { footprintEffect, ordinaryEffect, promiseEffect } from "./type-graph.mts";
import type { CallEffect, CallPromise } from "./type-graph.mts";

/** The projections a resolvable parameter owns: its observation and its
 * result. */
export function resolvableSlots(name: string): Within<{ value: "any"; store: "grow" }, { observation: string; result: string }> {
  return { observation: `#observe:${name}`, result: `#resolve:${name}` };
}

/** The projections a qualified parameter owns: an awaitable one its
 * observation, a resolvable one also its result. */
export function resolutionSlots(name: string, qualification: "awaitable" | "resolvable"): Within<{ value: "any"; store: "grow" }, ResolutionSlots> {
  return { observation: `#observe:${name}`, result: qualification === "resolvable" ? `#resolve:${name}` : null };
}

/** The names a qualified parameter's projections own. */
const ownedSlots = (slots: ResolutionSlots | null): Within<{ value: "any"; store: "grow" }, string[]> =>
  slots ? [slots.observation, ...(slots.result === null ? [] : [slots.result])] : [];

// Numeric literals in the fragment are plain decimals; every other spelling
// (hex, binary, octal, separators) is outside it. A bigint literal is read as
// its integer, whatever its spelling (`bigintText`).
const DECIMAL = /^[0-9]+(\.[0-9]+)?([eE][+-]?[0-9]+)?$/;

/** A term's parts, the terms it is made of, in the order of its fields:
 * the one traversal of the type-term grammar its folds use. */
export function typeParts(term: TypeTerm): Within<{ value: "any"; store: "grow" }, TypeTerm[]> {
  switch (term.k) {
    case "atom": case "literal": case "unique": case "callable": case "self": case "parameter": case "binder": return [];
    case "union": case "intersection": return term.parts;
    case "array": return [term.element];
    case "tuple": return [...term.required, ...term.optional, ...(term.rest ? [term.rest] : [])];
    case "object": return [...term.fields.map(field => field.type), ...term.calls,
      ...(term.stringIndex ? [term.stringIndex.value] : []), ...(term.numberIndex ? [term.numberIndex.value] : []),
      ...(term.symbolIndex ? [term.symbolIndex.value] : []), ...(term.prototype ? [term.prototype] : [])];
    case "function": return [...(term.receiver ? [term.receiver] : []), ...term.params,
      ...(term.rest ? [term.rest] : []), term.result];
    case "constructor": return [...term.params, ...(term.rest ? [term.rest] : []), term.result,
      ...(term.statics ?? []).map(field => field.type)];
    case "pack": return [term.of];
    case "reference": return term.args;
    case "scheme": return [...term.binders.flatMap(binder => [...(binder.bound ? [binder.bound] : []),
      ...(binder.default ? [binder.default] : [])]), ...term.signatures];
    default: { const exhaustive: never = term; return exhaustive; }
  }
}

/** Whether `term`, or a term it is made of, passes `test`. */
export function someType(term: TypeTerm, test: (term: TypeTerm) => Within<{ value: "any"; store: "grow" }, boolean>): Within<{ value: "any"; store: "grow" }, boolean> {
  return test(term) || typeParts(term).some(part => someType(part, test));
}

/** Visit every source type constructor, with the generic method binders in scope.
 * Readers use the same walk for annotation admissibility and name checking. */
export function visitType(term: TypeTerm, visit: (term: TypeTerm, bound: ReadonlySet<string>) => Within<{ value: "any"; store: "grow" }, void>,
    bound: ReadonlySet<string> = new Set()): Within<{ value: "any"; store: "grow" }, void> {
  visit(term, bound);
  // A scheme's binders are in scope in its bounds, defaults and signatures.
  let inner = bound;
  if (term.k === "scheme") {
    const scoped = new Set([...bound, ...term.binders.flatMap(binder => [binder.name, ...ownedSlots(binder.resolution)])]);
    inner = scoped;
  }
  for (const part of typeParts(term)) visitType(part, visit, inner);
}

/** Admissibility of a source annotation, independent of its input representation. */
export function validateAnnotation(term: TypeTerm, fail: (span: Span, message: string) => never): Within<{ value: "any"; store: "grow" }, void> {
  visitType(term, part => {
    if (part.k !== "intersection") return;
    const binder = (t: TypeTerm): boolean => t.k === "binder" || (t.k === "union" && t.parts.some(binder));
    for (const operand of part.parts) {
      if (operand.k === "atom" && (operand.name === "unknown" || operand.name === "never"))
        fail(operand.span, "an intersection operand must be a single type");
      if (operand.k === "union" && binder(operand))
        fail(part.span, "an intersection with a union holding a type parameter distributes into meets known " +
          "only at an instance: its meet has no representation");
    }
  });
}

/** A numeric literal's decimal lexeme: TypeScript's text of it, which
 * spells a hexadecimal, octal or binary literal and one with separators in
 * decimal, or, where that text is `Infinity` (a literal past the largest
 * double, `1e309`), the decimal source text, which rounds to the infinity.
 * None for a literal of neither form. */
export function numericLexeme(node: ts.NumericLiteral, source: SourceFile): Within<{ value: "any"; store: "grow" }, string | null> {
  if (DECIMAL.test(node.text)) return node.text;
  const written = source.getFullText().slice(node.getStart(source), node.end).replace(/_/g, "");
  return node.text === "Infinity" && DECIMAL.test(written) ? written : null;
}

/** A bigint literal's value as its canonical decimal integer: `0x10n`, `1_0n`
 * and `16n` are all `16`. */
export function bigintText(literal: string, negative: boolean): Within<{ value: "any"; store: "grow" }, string> {
  const value = BigInt(literal.slice(0, -1).replace(/_/g, ""));
  return String(negative ? -value : value);
}

/** `{}`, an object type with no member: it constrains no key, and is every
 * value but `null` and `undefined`, a primitive included, not an empty
 * record. */
function emptyObject(span: Span): Within<{ value: "any"; store: "grow" }, TypeTerm> {
  return { k: "union", span, parts: (["boolean", "number", "string", "bigint", "symbol", "object"] as const)
    .map(name => ({ k: "atom", name, span })) };
}

/** The property key a numeric literal names: `ToString` of its value, as
 * JavaScript converts it. */
export function numericKey(literal: string): Within<{ value: "any"; store: "grow" }, string> {
  return String(Number(literal.replace(/_/g, "")));
}

/** A generic method declaring `this: T`. A generic method's member is a
 * scheme its member bound to the host meets whatever receiver the bound
 * function is given (SOURCE-MODEL.md, "Method members are host-relative"), which
 * states no type the host must meet. */
export const GENERIC_METHOD_RECEIVER =
  "a generic method with a `this` parameter is outside the fragment: its member is a scheme the member bound to its host meets, which states no type the host must meet";

/** A method form's receiver: the declaration it is a member of, its host,
 * met with the type a `this` parameter states, which the host must meet. */
function hostReceiver(form: FunctionTerm, span: Span): Within<{ value: "any"; store: "grow" }, TypeTerm> {
  const self: TypeTerm = { k: "self", span };
  return form.receiver ? { k: "intersection", parts: [self, form.receiver], span } : self;
}

/** Why a class member of a kind the fragment has no lowering for is
 * refused. */
export function classMemberRefusal(member: ts.ClassElement): string {
  if (ts.isGetAccessorDeclaration(member) || ts.isSetAccessorDeclaration(member))
    return "a class accessor is outside the fragment: reading or writing it runs its code, where a member read or write in the model is a plain one";
  if (ts.isIndexSignatureDeclaration(member))
    return "an index signature in a class is outside the fragment: a class's instances are the objects its construction allocates, with the keys it names";
  if (ts.isClassStaticBlockDeclaration(member))
    return "a static block is outside the fragment: it is code the class definition runs, which the class's lowering does not have";
  return "a class member outside the fragment";
}

const REST_CONTRACT =
  "a rest parameter needs a tuple of required positions or an array";

/** A module function's rest typed by its own type parameter `T` that also
 * types something else. The array a call collects is fresh: it holds the
 * actuals and has none of `T`'s other members, so it is no value of `T` (at
 * `T = string[] & { tag: string }` it has no `tag`). */
export const REST_PACK_VALUE: string =
  `${REST_CONTRACT}: a type parameter typing a rest parameter and anything else would make the array a call ` +
  "collects a value of it, which it is not: the array is fresh, with the actuals and none of the " +
  "parameter's other members (at `string[] & { tag: string }` it has no `tag`)";

/** A module function's rest typed by its own type parameter whose bound is
 * no array or tuple of required positions written as one. */
export const REST_PACK_BOUND: string =
  `${REST_CONTRACT}: one typed by a type parameter collects the array its bound states, which must be ` +
  "written as an array or a tuple of required positions";

/** A rest parameter's type, a declared alias read through its equation at
 * the reference's arguments, as TypeScript reads one: the array a call
 * collects is viewed at that equation. */
export function restTerm(scope: TermScope, type: TypeTerm): Within<{ value: "any"; store: "grow" }, TypeTerm> {
  for (let seen = 0; type.k === "reference" && seen < 16; seen++) {
    const equation = scope.equation?.(type);
    if (!equation) break;
    type = equation;
  }
  return type;
}

/** Why a rest parameter's type is no contract for the array a call
 * collects, by its form. */
export function restRefusal(type: TypeTerm): Within<{ value: "any"; store: "grow" }, string> {
  switch (type.k) {
    case "parameter":
      return `${REST_CONTRACT}: one typed by a declaration's type parameter inside the declaration types its ` +
        "argument lists by a value type parameter's elements, which the heap holds, where an argument pack's " +
        "contract is heap-free";
    case "binder":
      return `${REST_CONTRACT}: one typed by a type parameter is an argument pack only in a function type or a ` +
        "module function, typed by its own parameter; a closure's scheme reads a bound as the meet of its binder " +
        "with it, and argument lists have no meet row";
    case "intersection":
      return `${REST_CONTRACT}: one typed by an intersection would view the fresh array a call collects at the ` +
        "meet of its operands, which has no representation";
    case "tuple":
      return `${REST_CONTRACT}: a tuple with optional or rest elements is several lengths, one signature each`;
    case "array": case "union": case "reference":
      return REST_CONTRACT;
    default:
      return `${REST_CONTRACT}: the array a call collects is no value of a type that is not an array`;
  }
}

export type TermScope = {
  source: SourceFile;
  fail(node: Node | null, message: string): never;
  /** A type reference: a binder in scope or a declaration. */
  named(node: TypeReferenceNode, span: Span, read: (node: TypeNode) => Within<{ value: "any"; store: "grow" }, TypeTerm>): Within<{ value: "any"; store: "grow" }, TypeTerm>;
  /** Whether a reference names the verifier's `Within` (`resolvable.d.ts`),
   * by the declaration TypeScript binds it to: a signature's statement of
   * its effect (`statedResult`). A scope without it reads no statement. */
  stated?(node: TypeReferenceNode): Within<{ value: "any"; store: "grow" }, boolean>;
  /** The resolved standard-library Awaited alias. Its associated projection
   * is read only through the enclosing descriptor scope. */
  awaited?: AwaitedHook;
  associated?(input: TypeTerm, span: Span, node: TypeReferenceNode): Within<{ value: "any"; store: "grow" }, TypeTerm>;
  /** A resolved associated-result alias expanded in this lexical scope. */
  associatedAlias?(node: TypeReferenceNode): Within<{ value: "any"; store: "grow" }, TypeAliasDeclaration | null>;
  expandingAliases?: Set<TypeAliasDeclaration>;
  /** An annotation states records as the source fragment always has: named,
   * required fields and at most one readonly string index. A declaration body
   * states what its equation says, and Lean decides what lowers. */
  annotation: boolean;
  /** The program's `exactOptionalPropertyTypes` under `strictNullChecks`,
   * which decides what `-?` makes of an optional field's type. A scope
   * without it reads `-?` only over a field whose type holds no
   * `undefined`. */
  exactOptional?: boolean;
  /** An external declaration's type-level wildcard being read, a type
   * parameter's constraint: the reading of each `any` in it by its span
   * (`wildcardReadings`). */
  wildcard?: ReadonlyMap<string, "unknown" | "never">;
  /** A declaration's own equation, when it is a type literal: its methods'
   * receiver is the declaration, as an interface's are. */
  body?: TypeNode;
  /** A computed key `[x]` or `[o.x]`: the index of the `unique symbol`
   * constant or readonly property it denotes. A scope without it reads no
   * symbol key. */
  symbol?(name: Identifier | ts.PropertyAccessExpression): Within<{ value: "any"; store: "grow" }, number>;
  /** A computed key `[x]` or `[o.x]` naming an entity of a string or number
   * literal type, as an enum member or a constant is: the key its value
   * names; null for any other. */
  literalKey?(name: Identifier | ts.PropertyAccessExpression): Within<{ value: "any"; store: "grow" }, string | null>;
  /** A class member's private name `#x`: the index of the symbol the
   * declaration document lists for it, a key no code outside the class
   * spells. A scope without it reads no private name. */
  privateName?(name: ts.PrivateIdentifier): Within<{ value: "any"; store: "grow" }, number>;
  /** `E.A` and `typeof E` for one of the file's enums: the member's literal
   * type and the enum's object type (SOURCE-CONTRACTS.md, "Enums"); null for any other
   * such node. A scope without it reads neither. */
  enumerated?: EnumeratedHook;
  /** A type TypeScript computes from other types (`COMPUTED`): `typeof x`,
   * `keyof T`, `T[K]`, a template literal type. The scope evaluates it to the
   * equivalent type the fragment states, or refuses it with the reason; `read`
   * reads an operand in this scope. A scope without it reads none. */
  computed?: ComputedHook;
  /** A mapped type's keys, or a library mapped type's key argument
   * (`Record<K, V>`), as the union of literals and primitives TypeScript
   * computes for it, `"a" | "b"` for an alias of those, or null. A scope
   * without it reads the keys as written. */
  keys?: KeysHook;
  /** A mapped type over `keyof X` at a finite record `X`: each property of
   * the type TypeScript resolves it to, with the modifiers it copies from
   * `X` and its own overrides, or null where TypeScript resolves no such
   * record. A scope without it reads only a mapped type writing both. */
  modifiers?: ModifiersHook;
  /** A reference to a declared type alias of an array, a tuple or another
   * alias: its equation at the reference's arguments, or null. A scope
   * without it reads no rest parameter through an alias. */
  equation?(reference: Extract<TypeTerm, { k: "reference" }>): Within<{ value: "any"; store: "grow" }, TypeTerm | null>;
  /** A named type's outer record shape, where the definitions it reaches
   * are complete (`recordShape`, named-record.mts): the record a mapped type
   * whose value is `X[P]` maps at a named X; null where they are not yet
   * complete. A scope without it, or answering null, defers the mapped type
   * (`deferredIdentity`). */
  record?: RecordHook;
  /** What a reference denotes where the definitions it reaches are
   * complete: `-?` without `exactOptionalPropertyTypes` takes `undefined`
   * from an alias's meaning. A scope without it, or answering null, defers
   * such a mapped type (`deferredIdentity`). */
  alias?: AliasHook;
};

/** The hooks of a scope its readers pass on or implement apart from it:
 * functions of their arguments, which take no receiver. */
export type AwaitedHook = (node: TypeReferenceNode) => Within<{ value: "any"; store: "grow" }, boolean>;
export type EnumeratedHook = (node: TypeNode, span: Span) => Within<{ value: "any"; store: "grow" }, TypeTerm | null>;
export type ComputedHook = (node: TypeNode, span: Span, read: (node: TypeNode) => Within<{ value: "any"; store: "grow" }, TypeTerm>) => Within<{ value: "any"; store: "grow" }, TypeTerm>;
export type KeysHook = (node: TypeNode) => Within<{ value: "any"; store: "grow" }, TypeTerm | null>;
export type ModifiersHook = (node: ts.MappedTypeNode) => Within<{ value: "any"; store: "grow" }, readonly MappedMember[] | null>;
export type RecordHook = (reference: Extract<TypeTerm, { k: "reference" }>, fail: (message: string) => never) => Within<{ value: "any"; store: "grow" }, TypeTerm | null>;
/** What a reference denotes, where the definitions it reaches are complete
 * (`aliasMeaning`, named-record.mts): `"record"` for a record written as one,
 * which holds no `undefined`, an alias's equation at the reference's
 * arguments otherwise; null where the definitions are not yet complete. */
export type AliasHook = (reference: Extract<TypeTerm, { k: "reference" }>, fail: (message: string) => never) => Within<{ value: "any"; store: "grow" }, TypeTerm | "record" | null>;

/** The type forms TypeScript computes from other types, as the syntax kind a
 * refusal names. Their meaning is the type TypeScript computes, which the
 * declaration reader evaluates (SOURCE-CONTRACTS.md, "Computed types"). */
export function computedForm(node: TypeNode): Within<{ value: "any"; store: "grow" }, string | null> {
  if (ts.isTypeQueryNode(node)) return "typeof";
  if (ts.isTypeOperatorNode(node) && node.operator === ts.SyntaxKind.KeyOfKeyword) return "keyof";
  if (ts.isIndexedAccessTypeNode(node)) return "an indexed access type";
  if (ts.isTemplateLiteralTypeNode(node)) return "a template literal type";
  if (ts.isConditionalTypeNode(node)) return "a conditional type";
  // `number & string` is `never`, `string & "a"` is `"a"`: TypeScript
  // reduces an intersection of primitives and literals.
  if (ts.isIntersectionTypeNode(node) && intersectionOperands(node).every(t =>
      ts.isLiteralTypeNode(t) || PRIMITIVE_KEYWORDS.includes(t.kind)))
    return "an intersection of primitives";
  return null;
}

/** A generic type alias whose equation is a type TypeScript computes
 * (`computedForm`), `type ElementOf<T> = T[number]`, `type Keys<T> = keyof T`,
 * or is an application of another such alias, or an application one of whose
 * arguments is such a type, `type Omit<T, K> = Pick<T, Exclude<keyof T, K>>`:
 * over its parameters it is known only at an application, so it has no
 * equation of its own, and each reference to it is a computed type, evaluated
 * at the reference's arguments (`computed-types.mts`). `aliasOf` is the alias
 * a reference names, if any. */
export function computedAlias(node: Node, aliasOf: (reference: TypeReferenceNode) => TypeAliasDeclaration | null,
    seen: Set<Node> = new Set()): node is TypeAliasDeclaration {
  if (!isTypeAlias(node) || !node.typeParameters?.length || seen.has(node)) return false;
  seen.add(node);
  const body = unwrap(node.type);
  if (computedForm(body) !== null) return true;
  if (!ts.isTypeReferenceNode(body)) return false;
  const computed = (reference: TypeReferenceNode): boolean => {
    const target = aliasOf(reference);
    return !!target && computedAlias(target, aliasOf, new Set(seen));
  };
  return computed(body) || (body.typeArguments ?? []).some(argument => {
    const a = unwrap(argument);
    return computedForm(a) !== null || (ts.isTypeReferenceNode(a) && computed(a));
  });
}

const PRIMITIVE_KEYWORDS: ts.SyntaxKind[] = [ts.SyntaxKind.NullKeyword, ts.SyntaxKind.UndefinedKeyword,
  ts.SyntaxKind.BooleanKeyword, ts.SyntaxKind.NumberKeyword, ts.SyntaxKind.StringKeyword,
  ts.SyntaxKind.BigIntKeyword, ts.SyntaxKind.SymbolKeyword, ts.SyntaxKind.VoidKeyword];

/** An intersection's operands, nested intersections and parentheses flattened. */
function intersectionOperands(node: ts.IntersectionTypeNode): Within<{ value: "any"; store: "grow" }, TypeNode[]> {
  const operands: TypeNode[] = [];
  const flatten = (t: TypeNode): void => {
    t = unwrap(t);
    if (ts.isIntersectionTypeNode(t)) t.types.forEach(flatten);
    else operands.push(t);
  };
  flatten(node);
  return operands;
}

type FunctionTerm = Extract<TypeTerm, { k: "function" }>;

const spanOf = (scope: TermScope, node: Node): Within<{ value: "any"; store: "grow" }, Span> => [node.getStart(scope.source), node.end];

const unwrap = (node: TypeNode): Within<{ value: "any"; store: "grow" }, TypeNode> => {
  while (ts.isParenthesizedTypeNode(node)) node = node.type;
  return node;
};

/** `x?: T` is `T | undefined` where the parameter is read: `undefined` is the
 * value bound when a call omits that position. */
export function optionalTerm(type: TypeTerm, span: Span): Within<{ value: "any"; store: "grow" }, TypeTerm> {
  return { k: "union", parts: [type, { k: "atom", name: "undefined", span }], span };
}

/** A rest parameter's reading as a signature (`restPositions`): its
 * positions, or the element of any number of further arguments. */
export type RestPositions = { k: "positions"; positions: TypeTerm[] } | { k: "element"; element: TypeTerm };

/** The rest parameter's contract as positions of the signature: a tuple of
 * required positions is a fixed number of further arguments, an array, mutable
 * or readonly, any number of them. Anything else has no reading as a
 * signature. `k` decides the arm. */
export function restPositions(type: TypeTerm): Within<{ value: "any"; store: "grow" }, RestPositions | null> {
  // The array a call collects is fresh: it is an array of its element, and
  // viewing it as `readonly` gives up only writes.
  if (type.k === "array") return { k: "element", element: type.element };
  if (type.k === "tuple" && !type.optional.length && type.rest === null)
    return { k: "positions", positions: type.required };
  return null;
}

/** The readings of each `any` in a type-level wildcard of an external
 * declaration, a type parameter's constraint, by its span: the top type at
 * its position, `unknown` at a positive one and `never` at a parameter's,
 * each parameter flipping the polarity, as the declarations a program is
 * checked against read it (`shadow-contracts.mts`). Such a type constrains
 * types; no value has it. */
export function wildcardReadings(node: Node, source: SourceFile): Map<string, "unknown" | "never"> {
  const readings = new Map<string, "unknown" | "never">();
  const visit = (n: Node, positive: boolean): void => {
    if (n.kind === ts.SyntaxKind.AnyKeyword) {
      readings.set(`${n.getStart(source)}:${n.end}`, positive ? "unknown" : "never");
      return;
    }
    if (ts.isParameterDeclaration(n)) {
      if (n.type) visit(n.type, !positive);
      return;
    }
    n.forEachChild(child => { visit(child, positive); });
  };
  visit(node, true);
  return readings;
}

export function typeTerm(scope: TermScope, node: TypeNode | undefined, at: Node | null = null): Within<{ value: "any"; store: "grow" }, TypeTerm> {
  const term = readTypeTerm(scope, node, at);
  const location = node ?? at;
  if (scope.annotation && location)
    validateAnnotation(term, (_span, message) => scope.fail(location, message));
  return term;
}

function readTypeTerm(scope: TermScope, node: TypeNode | undefined, at: Node | null): Within<{ value: "any"; store: "grow" }, TypeTerm> {
  if (!node) return scope.fail(at, "missing type annotation");
  const span = spanOf(scope, node);
  const atom = (name: Extract<TypeTerm, { k: "atom" }>["name"]): TypeTerm => ({ k: "atom", name, span });
  switch (node.kind) {
    case ts.SyntaxKind.NullKeyword: return atom("null");
    case ts.SyntaxKind.UndefinedKeyword: return atom("undefined");
    case ts.SyntaxKind.BooleanKeyword: return atom("boolean");
    case ts.SyntaxKind.NumberKeyword: return atom("number");
    case ts.SyntaxKind.StringKeyword: return atom("string");
    case ts.SyntaxKind.BigIntKeyword: return atom("bigint");
    case ts.SyntaxKind.SymbolKeyword: return atom("symbol");
    case ts.SyntaxKind.UnknownKeyword: return atom("unknown");
    // A declaration's `any` constrains nothing, and `unknown` says exactly
    // that: what the library returns at it is assumed to be anything, and what
    // it accepts at it may be anything. TypeScript's `any` also converts to
    // every type; nothing here inherits that. An annotation of the checked
    // source states its own types, and `any` stays outside them.
    case ts.SyntaxKind.AnyKeyword:
      if (!scope.annotation) return atom(scope.wildcard?.get(spanOf(scope, node).join(":")) ?? "unknown");
      break;
    case ts.SyntaxKind.NeverKeyword: return atom("never");
    case ts.SyntaxKind.VoidKeyword: return atom("void");
    case ts.SyntaxKind.ObjectKeyword: return atom("object");
  }
  if (ts.isTypeLiteralNode(node) && !node.members.length) return emptyObject(span);
  if (ts.isParenthesizedTypeNode(node)) return typeTerm(scope, node.type);
  if (ts.isUnionTypeNode(node))
    return { k: "union", parts: node.types.map(t => typeTerm(scope, t)), span };
  if (ts.isIntersectionTypeNode(node)) return intersection(scope, node, span);
  if (ts.isArrayTypeNode(node))
    return { k: "array", presence: "readable", readonly: false, element: typeTerm(scope, node.elementType), span };
  if (ts.isTupleTypeNode(node)) return tuple(scope, node, false, span);
  if (ts.isTypeOperatorNode(node) && node.operator === ts.SyntaxKind.ReadonlyKeyword) {
    // `readonly T[]` and `readonly [..]`: the same contract as a view.
    const inner = unwrap(node.type);
    if (ts.isArrayTypeNode(inner))
      return { k: "array", presence: "readable", readonly: true, element: typeTerm(scope, inner.elementType), span };
    if (ts.isTupleTypeNode(inner)) return tuple(scope, inner, true, span);
    return scope.fail(node, "readonly applies to an array or tuple type");
  }
  // `unique symbol`, which TypeScript admits only on a constant or a readonly
  // static, is the type of that one symbol: read here, as an annotation, it
  // is a symbol. Which symbol it is, a key types name, is the declaration's
  // identity (`symbols` of the declaration document); an imported constant's
  // value is that singleton (`valueOf` in `declaration-graph.mts`).
  if (ts.isTypeOperatorNode(node) && node.operator === ts.SyntaxKind.UniqueKeyword &&
      unwrap(node.type).kind === ts.SyntaxKind.SymbolKeyword)
    return atom("symbol");
  if (ts.isLiteralTypeNode(node)) {
    // `literal` is declared as a bare Node, so it too is read by predicate.
    const literal = node.literal;
    if (literal.kind === ts.SyntaxKind.NullKeyword) return atom("null");
    if (literal.kind === ts.SyntaxKind.TrueKeyword || literal.kind === ts.SyntaxKind.FalseKeyword)
      return { k: "literal", name: literal.kind === ts.SyntaxKind.TrueKeyword ? "true" : "false",
        text: literal.kind === ts.SyntaxKind.TrueKeyword ? "true" : "false", span };
    // The literal's value: a string without its quotes, a number as its
    // decimal spelling.
    // A template without holes, `\`a\rb\``, is its cooked string, as a
    // template expression's is.
    if (ts.isStringLiteral(literal) || ts.isNoSubstitutionTemplateLiteral(literal))
      return { k: "literal", name: "string", text: literal.text, span };
    // A numeric literal type, possibly negated (`-1`, `-5n`).
    const negated = ts.isPrefixUnaryExpression(literal) &&
      literal.operator === ts.SyntaxKind.MinusToken ? literal.operand : null;
    const numeric = negated ?? literal;
    if (ts.isNumericLiteral(numeric)) {
      const lexeme = numericLexeme(numeric, scope.source);
      if (lexeme === null) scope.fail(literal, "non-decimal numeric literal type");
      return { k: "literal", name: "number", text: (negated ? "-" : "") + lexeme, span };
    }
    if (ts.isBigIntLiteral(numeric))
      return { k: "literal", name: "bigint", text: bigintText(numeric.text, negated !== null), span };
    return scope.fail(literal, "literal type outside the fragment");
  }
  // A type literal of construct signatures only, `{ new (): T }`, is the
  // constructor type they state, as `new () => T` is; several are overloads,
  // each a construct signature of the one value.
  if (ts.isTypeLiteralNode(node) && node.members.length &&
      node.members.every(ts.isConstructSignatureDeclaration)) {
    const forms = node.members.flatMap(m => ts.isConstructSignatureDeclaration(m) ? constructorForms(scope, m, span) : []);
    const [only] = forms;
    return forms.length === 1 && only ? only : { k: "intersection", parts: forms, span };
  }
  if (ts.isTypeLiteralNode(node))
    return members(scope, node.members, node, span, node === scope.body ? true : "nested");
  if (ts.isMappedTypeNode(node))
    return expandMapped(mapped(scope, node), span, message => scope.fail(node, message), scope.record, scope.alias);
  if (ts.isFunctionTypeNode(node)) {
    // A rest admitting no argument list, `(...args: never) => R`: no call
    // is possible, and the type is every value with call code.
    const last = node.parameters[node.parameters.length - 1];
    if (!node.typeParameters?.length && last?.dotDotDotToken && last.type) {
      const rest = typeTerm(scope, last.type, last);
      if (rest.k === "atom" && rest.name === "never") return atom("function");
    }
    if (!node.typeParameters?.length) return oneTerm(signatures(scope, node.parameters, node.type, node, span), span);
    // A generic function type, `<A>(x: A) => R`, in a declaration or an
    // annotation, is a scheme whose signatures take any receiver, or the one
    // a `this` parameter states.
    if (!node.type) scope.fail(node, "generic function types are outside the fragment");
    const { binders, forms } = quantified(scope, node.typeParameters, node.parameters, node.type, node, span);
    return { k: "scheme", binders,
      signatures: forms.map(m => ({ ...m, receiver: m.receiver ?? { k: "atom", name: "unknown", span } })), span };
  }
  // `new (params) => R`: a construct signature per accepted argument list. It
  // has no receiver; its rest, if any, is a function's.
  if (ts.isConstructorTypeNode(node)) {
    // A rest admitting no argument list, `abstract new (...args: never) => R`:
    // no construction is possible, and the type is every class value.
    const last = node.parameters[node.parameters.length - 1];
    if (!node.typeParameters?.length && last?.dotDotDotToken && last.type) {
      const rest = typeTerm(scope, last.type, last);
      if (rest.k === "atom" && rest.name === "never") return atom("class");
    }
    const forms = constructorForms(scope, node, span);
    const [only] = forms;
    return forms.length === 1 && only ? only : { k: "intersection", parts: forms, span };
  }
  if ((ts.isTypeReferenceNode(node) && node.typeName.kind !== ts.SyntaxKind.Identifier) || ts.isTypeQueryNode(node)) {
    const enumerated = scope.enumerated?.(node, span);
    if (enumerated) return enumerated;
  }
  // A qualified name is the scope's to read (a namespace member), or to refuse.
  if (ts.isTypeReferenceNode(node)) {
    if (scope.stated?.(node))
      return scope.fail(node, WITHIN_PLACE);
    if (scope.awaited?.(node)) {
      const [argument, ...others] = node.typeArguments ?? [];
      if (!argument || others.length) return scope.fail(node, "Awaited requires one type argument");
      if (!scope.associated) return scope.fail(node, "Awaited requires a resolution-qualified scope");
      return scope.associated(typeTerm(scope, argument), span, node);
    }
    const alias = scope.associatedAlias?.(node);
    if (alias) {
      if (scope.expandingAliases?.has(alias)) return scope.fail(node,
        "a recursive associated-result alias is outside the fragment");
      const parameters = alias.typeParameters ?? [];
      const arguments_ = node.typeArguments ?? [];
      if (arguments_.length !== parameters.length || parameters.some(p => p.constraint || p.defaultType))
        return scope.fail(node, "an associated-result alias requires all unbounded arguments explicitly");
      const inputs = arguments_.map(argument => typeTerm(scope, argument));
      const expandingAliases = new Set(scope.expandingAliases ?? []);
      expandingAliases.add(alias);
      const inner: TermScope = { ...scope, source: alias.getSourceFile(), expandingAliases,
        awaited: reference => {
          const name = reference.typeName;
          return !(ts.isIdentifier(name) && parameters.some(p => p.name.text === name.text)) &&
            (scope.awaited?.(reference) ?? false);
        },
        associatedAlias: reference => {
          const name = reference.typeName;
          return ts.isIdentifier(name) && parameters.some(p => p.name.text === name.text)
            ? null : scope.associatedAlias?.(reference) ?? null;
        },
        named(reference, position, read) {
          const name = reference.typeName;
          const index = ts.isIdentifier(name)
            ? parameters.findIndex(p => p.name.text === name.text) : -1;
          if (index < 0) return scope.named(reference, position, read);
          const input = inputs[index];
          if (!input || reference.typeArguments?.length) return scope.fail(reference,
            "an alias parameter takes no type arguments");
          return input;
        } };
      return typeTerm(inner, alias.type, alias);
    }
    return scope.named(node, span, part => typeTerm(scope, part));
  }
  if (computedForm(node) !== null && scope.computed)
    return scope.computed(node, span, part => typeTerm(scope, part));
  // `x is T` and `asserts x is T` are a signature's result only, which
  // `signatures` reads as a promise signature beside the plain one.
  if (ts.isTypePredicateNode(node))
    return scope.fail(node, "a type predicate (`x is T`) is a function's result, which states it as a promise about a parameter");
  return scope.fail(node, `type outside the fragment (${ts.SyntaxKind[node.kind]})`);
}

/** A construct signature's forms, one per accepted argument list: it has no
 * receiver, and its rest, if any, is a function's. */
function constructorForms(scope: TermScope, node: ts.ConstructorTypeNode | ts.ConstructSignatureDeclaration,
    span: Span): Within<{ value: "any"; store: "grow" }, TypeTerm[]> {
  if (ts.isConstructorTypeNode(node) && node.modifiers?.length)
    scope.fail(node, "an abstract constructor type is outside the fragment");
  if (!node.type) scope.fail(node, "a constructor type needs its result type");
  const construct = (f: FunctionTerm): Extract<TypeTerm, { k: "constructor" }> => {
    if (f.receiver) scope.fail(node, "a constructor type has no receiver");
    return { k: "constructor", effect: f.effect, params: f.params, rest: f.rest, result: f.result, span };
  };
  // A generic construct signature, `new <A>(x: A) => C<A>`, is a scheme of
  // construct signatures: a class value meeting each at every instance.
  if (node.typeParameters?.length) {
    const { binders, forms } = quantified(scope, node.typeParameters, node.parameters, node.type, node, span);
    return [{ k: "scheme", binders, signatures: forms.map(construct), span }];
  }
  return signatures(scope, node.parameters, node.type, node, span).map(construct);
}

/** A mapped type `{ [P in K]: V }` whose value does not name its key `P`:
 * the key and value terms as read, and its modifiers. Over a key union
 * nothing is copied, so a `-` modifier states nothing; over `keyof X`, X's
 * are copied where none is written, and each member's are TypeScript's. */
export type Mapped = { key: TypeTerm; value: TypeTerm; optional: boolean; readonly: boolean;
  members?: readonly MappedMember[]; identity?: Identity };
/** A mapped type whose value is `X[P]`, `P` its key and `X` a type that
 * names no `P`: over `keyof X`, X's own members and indexes (`Readonly`,
 * `Partial`, `Required`); over a key union `K`, the fields of X that K names
 * (`Pick`). Each modifier is added (`+`, or written alone), removed (`-`), or
 * kept from X where none is written. `exact` is whether the program reads
 * an optional property's type exactly (`exactOptionalPropertyTypes`), which
 * decides the value type `-?` gives an optional field; null where the scope
 * reading the mapped type does not state the program's option. */
export type Identity = { object: TypeTerm; homomorphic: boolean; readonlyMod: Modifier; optionalMod: Modifier;
  exact: boolean | null };
export type Modifier = "keep" | "add" | "remove";
/** A property of a mapped type over `keyof X` and its modifiers. */
export type MappedMember = { name: string; optional: boolean; readonly: boolean };

export function mapped(scope: TermScope, node: ts.MappedTypeNode): Within<{ value: "any"; store: "grow" }, Mapped> {
  if (node.nameType) scope.fail(node, "a mapped type with an 'as' clause is outside the fragment");
  if (node.members?.length) scope.fail(node, "a mapped type with members is outside the fragment");
  const parameter = node.typeParameter;
  const name = parameter.name.text;
  const names = (t: Node): boolean =>
    (ts.isTypeReferenceNode(t) && ts.isIdentifier(t.typeName) && t.typeName.text === name) ||
    (t.forEachChild(names) ?? false);
  const modifier = (token: Node | undefined): Modifier =>
    !token ? "keep" : token.kind === ts.SyntaxKind.MinusToken ? "remove" : "add";
  // `{ [P in keyof X]: X[P] }` or `{ [P in K]: X[P] }`: the value indexes a
  // type naming no `P` by the key itself.
  const value = node.type;
  const constraint0 = parameter.constraint;
  if (value && ts.isIndexedAccessTypeNode(value) && ts.isTypeReferenceNode(value.indexType) &&
      ts.isIdentifier(value.indexType.typeName) && value.indexType.typeName.text === name && !value.indexType.typeArguments &&
      !names(value.objectType) && constraint0) {
    // The same type written twice: the same nodes, leaves spelled alike.
    const same = (a: Node, b: Node): boolean => {
      if (a.kind !== b.kind) return false;
      const as: Node[] = [], bs: Node[] = [];
      a.forEachChild(c => void as.push(c));
      b.forEachChild(c => void bs.push(c));
      if (!as.length && !bs.length) return a.getText(a.getSourceFile()) === b.getText(b.getSourceFile());
      return as.length === bs.length && as.every((c, i) => { const d = bs[i]; return !!d && same(c, d); });
    };
    const keyofObject = (t: TypeNode | undefined): boolean => !!t && ts.isTypeOperatorNode(t) &&
      t.operator === ts.SyntaxKind.KeyOfKeyword && same(t.type, value.objectType);
    const homomorphic = keyofObject(constraint0);
    // Over a type parameter bounded by `keyof X` (`Pick`'s `K`) TypeScript
    // copies X's modifiers too; over any other key union it copies none,
    // and that form is refused below.
    const bound = (t: TypeNode): TypeNode | undefined => {
      if (!ts.isTypeReferenceNode(t) || !ts.isIdentifier(t.typeName) || t.typeArguments) return undefined;
      const k = t.typeName.text;
      for (let n: Node | undefined = node.parent; n; n = n.parent) {
        const own = (isTypeAlias(n) || ts.isInterfaceDeclaration(n) ? n.typeParameters : undefined)
          ?.find(q => q.name.text === k);
        if (own) return own.constraint;
      }
      return undefined;
    };
    if (homomorphic || keyofObject(bound(constraint0))) {
    const object = typeTerm(scope, value.objectType);
    // Over `keyof X` the keys are X's own, read from X when it is known;
    // the key term then names nothing.
    const key: TypeTerm = homomorphic ? { k: "atom", name: "never", span: [constraint0.pos, constraint0.end] }
      : scope.keys?.(constraint0) ?? typeTerm(scope, constraint0, parameter);
    return { key, value: object, optional: false, readonly: false,
      identity: { object, homomorphic, readonlyMod: modifier(node.readonlyToken), optionalMod: modifier(node.questionToken),
        exact: scope.exactOptional ?? null } };
    }
  }
  if (!node.type || names(node.type)) scope.fail(node, "a mapped type's value names its key");
  // A homomorphic mapped type, `{ [P in keyof X]: V }`, copies X's
  // modifiers to each key where it writes none of its own: each member at
  // the modifiers TypeScript resolves.
  const constraint = parameter.constraint;
  const members = constraint && ts.isTypeOperatorNode(constraint) &&
      constraint.operator === ts.SyntaxKind.KeyOfKeyword && (!node.readonlyToken || !node.questionToken)
    ? scope.modifiers?.(node) ?? scope.fail(node, "a mapped type over `keyof` copies its source's modifiers " +
      "where it writes none, and TypeScript resolves it to no record whose members state them")
    : undefined;
  const plus = (token: Node | undefined, keyword: ts.SyntaxKind) =>
    !!token && (token.kind === keyword || token.kind === ts.SyntaxKind.PlusToken);
  const key = parameter.constraint && scope.keys?.(parameter.constraint);
  return { key: key ?? typeTerm(scope, parameter.constraint, parameter), value: typeTerm(scope, node.type),
    optional: plus(node.questionToken, ts.SyntaxKind.QuestionToken),
    readonly: plus(node.readonlyToken, ts.SyntaxKind.ReadonlyKeyword), ...(members ? { members } : {}) };
}

/** A mapped type at a known key, as TypeScript expands it: over string and
 * number literals, one field per property they name; over `string`, a string
 * index, which `number` and every string literal add nothing to; over
 * `number`, a number index, which number literals add nothing to; over
 * `symbol`, a symbol index. Its value does not name the key, so every field
 * and index has the one value type. A type parameter is refused. */
export function expandMapped(m: Mapped, span: Span, fail: (message: string) => never,
    record?: RecordHook, alias?: AliasHook): Within<{ value: "any"; store: "grow" }, TypeTerm> {
  if (m.identity) return expandIdentity(m.identity, m.key, span, fail, record, alias);
  const keys: TypeTerm[] = [];
  const flatten = (t: TypeTerm): void => {
    if (t.k === "union") t.parts.forEach(flatten);
    else if (!(t.k === "atom" && t.name === "never")) keys.push(t);
  };
  flatten(m.key);
  const atom = (name: string) => keys.some(k => k.k === "atom" && k.name === name);
  const index = { readonly: m.readonly, value: m.value, span };
  const indexes = {
    // `string` absorbs every string and number key, `number` every number
    // literal.
    stringIndex: atom("string") ? index : null,
    ...(atom("number") && !atom("string") ? { numberIndex: index } : {}),
    ...(atom("symbol") ? { symbolIndex: index } : {}),
  };
  if (atom("string") || atom("number") || atom("symbol")) {
    if (m.members) fail("a mapped type over `keyof` an indexed type copies its index modifiers, which the reader does not read");
    if (keys.some(k => !(k.k === "atom" && (k.name === "string" || k.name === "number" || k.name === "symbol")) &&
        !(k.k === "literal" && (k.name === "string" || k.name === "number"))))
      fail("a mapped type's keys must be strings, numbers, symbols or their literals");
    if (m.optional) fail("an optional mapped type over an index signature's keys is outside the fragment");
  }
  const names: string[] = [];
  for (const key of keys) {
    if (key.k === "atom" && (key.name === "string" || key.name === "number" || key.name === "symbol")) continue;
    // An index over every string or number key holds its literals.
    if (atom("string") || (atom("number") && key.k === "literal" && key.name === "number")) continue;
    // A number literal key is the property its value names.
    const name = key.k === "literal" && key.name === "string" ? key.text
      : key.k === "literal" && key.name === "number" ? numericKey(key.text) : null;
    if (name === null) return fail("a mapped type's keys must be string or string literals");
    if (!names.includes(name)) names.push(name);
  }
  // No key: an object type with no member, which is `{}`.
  if (!names.length && !atom("string") && !atom("number") && !atom("symbol")) return emptyObject(span);
  return { k: "object", fields: names.map(name => {
    const member = m.members ? m.members.find(x => x.name === name)
      ?? fail(`TypeScript resolves the mapped type over \`keyof\` with no member ${name}`) : m;
    return { name, optional: member.optional, readonly: member.readonly, type: m.value, span };
  }), ...indexes, calls: [], span };
}

/** The module of a deferred mapped type's marker (`deferredIdentity`): no
 * declaration has it, since every module identity is a path
 * (`DeclarationIdentity`). */
export const DEFERRED_MODULE = "#deferred-mapped-identity";

/** A mapped type whose value is `X[P]` at a named X, read where the
 * definitions X reaches are not yet complete: a reference to no
 * declaration, of module `DEFERRED_MODULE`, whose target's name spells the
 * mapping's form and modifiers and whose arguments are X and the key. A
 * term of the wire's type holds it so that substitution and every traversal
 * carry it; each is replaced by its expansion once the definitions are
 * complete (`settleTerm`, named-record.mts), and a document holding one is
 * refused (`deferredIn`). */
export function deferredIdentity(id: Identity, key: TypeTerm, span: Span): Within<{ value: "any"; store: "grow" }, TypeTerm> {
  return { k: "reference", span, args: [id.object, key], reference: { name: "a mapped type over a named type", span,
    arguments: [], target: { module: DEFERRED_MODULE,
      name: `${id.homomorphic ? "keyof" : "pick"}:${id.readonlyMod}:${id.optionalMod}:${String(id.exact)}`, span } } };
}

const exactOf = (text: string | undefined): boolean | null | undefined =>
  text === "true" ? true : text === "false" ? false : text === "null" ? null : undefined;

const isModifier = (text: string | undefined): text is Modifier =>
  text === "keep" || text === "add" || text === "remove";

/** A deferred mapped type's identity and key (`deferredIdentity`), or null
 * for any other term. */
export function deferredOf(term: TypeTerm): Within<{ value: "any"; store: "grow" }, { identity: Identity; key: TypeTerm } | null> {
  if (term.k !== "reference" || term.reference.target.module !== DEFERRED_MODULE) return null;
  const [form, readonlyMod, optionalMod, exactText, ...rest] = term.reference.target.name.split(":");
  const [object, key, ...more] = term.args;
  const exact = exactOf(exactText);
  if ((form !== "keyof" && form !== "pick") || !isModifier(readonlyMod) || !isModifier(optionalMod) || exact === undefined ||
      rest.length || !object || !key || more.length)
    throw Error(`a malformed deferred mapped type: ${term.reference.target.name}`);
  return { identity: { object, homomorphic: form === "keyof", readonlyMod, optionalMod, exact }, key };
}

/** A mapped type whose value is `X[P]` at a known X: X's members (all of
 * them over `keyof X`, the fields its key union names otherwise) with the
 * modifiers the mapping adds or removes. X is a record type written as one,
 * or a named type, read at its outer record shape where `record` gives it
 * (`recordShape`) and deferred where the definitions it reaches are not yet
 * complete; a union or a type parameter is refused. */
function expandIdentity(id: Identity, key: TypeTerm, span: Span, fail: (message: string) => never,
    record?: RecordHook, alias?: AliasHook): Within<{ value: "any"; store: "grow" }, TypeTerm> {
  let x = id.object;
  if (x.k === "reference") {
    const shape = record?.(x, fail) ?? null;
    if (!shape) return deferredIdentity(id, key, span);
    x = shape;
  }
  if (x.k !== "object") return fail("a mapped type's value names its key, over a type that is no record the reader holds");
  if (x.calls.length || x.prototype || x.host || x.stable)
    return fail("a mapped type's value names its key, over a type with call signatures, a prototype or a host's members");
  // A method's receiver is the declaration it is a member of: mapped, the
  // member is a field of another type, of which no receiver is stated.
  let receiver = false;
  for (const f of x.fields) visitType(f.type, part => { if (part.k === "self") receiver = true; });
  if (receiver) return fail("a mapped type's value names its key, over a type with a method whose receiver is that type");
  const apply = (mod: Modifier, own: boolean): boolean => (mod === "keep" ? own : mod === "add");
  const readonly = (own: boolean): boolean => apply(id.readonlyMod, own);
  const optional = (own: boolean): boolean => apply(id.optionalMod, own);
  // `-?` keeps an optional field's type where `exactOptionalPropertyTypes`
  // is on, and takes `undefined` from it where it is off (`withoutUndefined`).
  // A scope stating no option refuses every field whose type may hold
  // `undefined`.
  const value = (f: { optional: boolean; type: TypeTerm }): TypeTerm | null =>
    !f.optional || id.optionalMod !== "remove" || !mayHoldUndefined(f.type) || id.exact === true ? f.type
      : id.exact === false ? withoutUndefined(f.type, fail, alias)
      : fail("`-?` over an optional field whose type may hold undefined, whose meaning depends on exactOptionalPropertyTypes, is outside the fragment");
  const settled = (values: (TypeTerm | null)[]): values is TypeTerm[] => values.every(v => v !== null);
  if (id.homomorphic) {
    if ((x.stringIndex || x.numberIndex || x.symbolIndex) && id.optionalMod === "add")
      return fail("an optional mapped type over an index signature's keys is outside the fragment");
    // No member: `{}`, every value but null and undefined, as TypeScript
    // reads a mapped type over an empty record.
    if (!x.fields.length && !x.stringIndex && !x.numberIndex && !x.symbolIndex) return emptyObject(span);
    const values = x.fields.map(value);
    if (!settled(values)) return deferredIdentity(id, key, span);
    return { ...x, fields: x.fields.map((f, i) => ({ ...f, type: values[i] ?? f.type, readonly: readonly(f.readonly), optional: optional(f.optional) })),
      stringIndex: x.stringIndex && { ...x.stringIndex, readonly: readonly(x.stringIndex.readonly) },
      ...(x.numberIndex ? { numberIndex: { ...x.numberIndex, readonly: readonly(x.numberIndex.readonly) } } : {}),
      ...(x.symbolIndex ? { symbolIndex: { ...x.symbolIndex, readonly: readonly(x.symbolIndex.readonly) } } : {}), span };
  }
  // A key union: each literal names a field of X.
  const names: PropertyKey[] = [];
  const collect = (k: TypeTerm): void => {
    if (k.k === "union") k.parts.forEach(collect);
    else if (k.k === "literal" && k.name === "string") names.push(k.text);
    else if (k.k === "literal" && k.name === "number") names.push(numericKey(k.text));
    else if (!(k.k === "atom" && k.name === "never")) fail("a mapped type's value names its key, over keys that are not literals");
  };
  collect(key);
  // No key: `{}`, every value but null and undefined.
  if (!names.length) return emptyObject(span);
  const fields = names.map(n => x.fields.find(f => f.name === n) ?? fail(`a mapped type's value names its key, and the record has no field ${String(n)}`));
  const values = fields.map(value);
  if (!settled(values)) return deferredIdentity(id, key, span);
  return { k: "object", fields: fields.map((f, i) => ({ ...f, type: values[i] ?? f.type, readonly: readonly(f.readonly), optional: optional(f.optional), span })),
    stringIndex: null, calls: [], span };
}

const undefinedAtom = (t: TypeTerm): boolean => t.k === "atom" && (t.name === "undefined" || t.name === "void");
/** Whether a term may hold `undefined` as far as its own form tells: a
 * type parameter, a reference and an intersection may. */
const mayHoldUndefined = (t: TypeTerm): boolean =>
  t.k === "union" ? t.parts.some(mayHoldUndefined)
    : t.k === "atom" ? undefinedAtom(t) || t.name === "unknown"
    : t.k === "binder" || t.k === "parameter" || t.k === "reference" || t.k === "intersection" || t.k === "self" || t.k === "pack";
const unionParts = (t: TypeTerm): TypeTerm[] => (t.k === "union" ? t.parts.flatMap(unionParts) : [t]);

/** An optional field's type as `-?` reads it without
 * `exactOptionalPropertyTypes`: TypeScript's type with `undefined` taken
 * away. Each `undefined` and `void` of its union is dropped (`never` where
 * none is left); a reference to a record written as one is kept, and one to
 * an alias is its meaning (`alias`) with `undefined` taken away, kept as
 * written where that meaning holds none. Any other part that may hold
 * `undefined` (a type parameter, an intersection, `unknown`) is refused.
 * Null where a reference's meaning is not yet known: the mapped type is
 * deferred. */
function withoutUndefined(t: TypeTerm, fail: (message: string) => never, alias?: AliasHook):
    Within<{ value: "any"; store: "grow" }, TypeTerm | null> {
  const strip = (term: TypeTerm, depth: number): { term: TypeTerm; changed: boolean } | null => {
    if (depth > 16) return fail("`-?` over an optional field whose type reaches more than 16 aliases is outside the fragment");
    const kept: TypeTerm[] = [];
    let changed = false;
    for (const part of unionParts(term)) {
      if (undefinedAtom(part)) {
        changed = true;
        continue;
      }
      if (part.k === "reference" && part.reference.target.module !== DEFERRED_MODULE) {
        const meaning = alias?.(part, fail) ?? null;
        if (meaning === null) return null;
        if (meaning === "record") {
          kept.push(part);
          continue;
        }
        const inner = strip(meaning, depth + 1);
        if (!inner) return null;
        if (!inner.changed) kept.push(part);
        else {
          changed = true;
          kept.push(...unionParts(inner.term).filter(p => !(p.k === "atom" && p.name === "never")));
        }
        continue;
      }
      if (mayHoldUndefined(part))
        return fail("`-?` over an optional field whose type may hold undefined as a type parameter, an intersection or " +
          "`unknown`, which TypeScript takes undefined from without exactOptionalPropertyTypes, is outside the fragment");
      kept.push(part);
    }
    const [only] = kept;
    return { changed, term: !only ? { k: "atom", name: "never", span: term.span }
      : kept.length === 1 ? only : { k: "union", parts: kept, span: term.span } };
  };
  return strip(t, 0)?.term ?? null;
}

/** `term` with each of its declaration's parameters replaced by the term at
 * that position of `args`. */
export function substitute(term: TypeTerm, args: readonly TypeTerm[]): Within<{ value: "any"; store: "grow" }, TypeTerm> {
  if (term.k === "parameter") {
    const arg = args[term.index];
    if (!arg) throw Error("declaration parameter index outside its application");
    return arg;
  }
  return mapTypeParts(term, part => substitute(part, args));
}

/** A term's parts each mapped by `go`. */
export function mapTypeParts(term: TypeTerm, go: (part: TypeTerm) => Within<{ value: "any"; store: "grow" }, TypeTerm>): Within<{ value: "any"; store: "grow" }, TypeTerm> {
  type FunctionTerm = Extract<TypeTerm, { k: "function" }>;
  const fn = (f: FunctionTerm): FunctionTerm => ({ ...f, receiver: f.receiver && go(f.receiver),
    params: f.params.map(go), rest: f.rest && go(f.rest), result: go(f.result) });
  const ctor = (c: Extract<TypeTerm, { k: "constructor" }>): Extract<TypeTerm, { k: "constructor" }> =>
    ({ ...c, params: c.params.map(go), rest: c.rest && go(c.rest), result: go(c.result),
      ...(c.statics ? { statics: c.statics.map(s => ({ ...s, type: go(s.type) })) } : {}) });
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
    case "constructor": return ctor(term);
    case "pack": return { ...term, of: go(term.of) };
    case "scheme": return { ...term, binders: term.binders.map(b => ({ ...b, bound: b.bound && go(b.bound),
      default: b.default && go(b.default) })), signatures: term.signatures.map(f => f.k === "function" ? fn(f)
        : ctor(f)) };
    case "reference": return { ...term, args: term.args.map(go) };
  }
}

/** A tuple element's kind and type, read through its name when it has one. */
function tupleMember(element: TypeNode): Within<{ value: "any"; store: "grow" }, { kind: "required" | "optional" | "rest"; type: TypeNode }> {
  if (ts.isNamedTupleMember(element))
    return { kind: element.dotDotDotToken ? "rest" : element.questionToken ? "optional" : "required",
      type: element.type };
  if (ts.isRestTypeNode(element)) return { kind: "rest", type: element.type };
  if (ts.isOptionalTypeNode(element)) return { kind: "optional", type: element.type };
  return { kind: "required", type: element };
}

function tuple(scope: TermScope, node: ts.TupleTypeNode, readonly: boolean, span: Span): Within<{ value: "any"; store: "grow" }, TypeTerm> {
  const required: TypeTerm[] = [], optional: TypeTerm[] = [];
  let rest: TypeTerm | null = null;
  for (const element of node.elements) {
    // A member's name is a label with no runtime meaning: `[start: number]`
    // is `[number]`, `[a?: T]` is `[T?]` and `[...rest: T[]]` is `[...T[]]`.
    const member = tupleMember(element);
    if (member.kind === "rest") {
      if (rest !== null || !ts.isArrayTypeNode(member.type))
        scope.fail(element, "a tuple rest must be one final array");
      rest = typeTerm(scope, member.type.elementType);
    } else if (member.kind === "optional") {
      if (rest !== null) scope.fail(element, "an optional position cannot follow the rest");
      optional.push(typeTerm(scope, member.type));
    } else {
      if (optional.length || rest !== null)
        scope.fail(element, "a required position cannot follow an optional one");
      required.push(typeTerm(scope, member.type));
    }
  }
  return { k: "tuple", presence: "dense", readonly, required, optional, rest, span };
}

/** Union is a list of parts; an intersection's operands are met in Lean,
 * which refuses a meet it cannot represent: record and function operands are
 * one location under several contracts or one function with several
 * signatures, any other ground operands the graph's meet of their rows, and a
 * type parameter with others the meet row of its parameter row within them
 * (`T & U`, `T & "fixed"`). An annotation's union operand holding a type
 * parameter, `(T | null) & A`, is refused: it would distribute into meets
 * each known only at an instance. */
function intersection(scope: TermScope, node: ts.IntersectionTypeNode, span: Span): Within<{ value: "any"; store: "grow" }, TypeTerm> {
  if (computedForm(node) !== null && scope.computed)
    return scope.computed(node, span, part => typeTerm(scope, part));
  const operands = intersectionOperands(node);
  const parts = operands.map(operand => typeTerm(scope, operand));
  return { k: "intersection", parts, span };
}

/** A signature's parameters: a leading `this: T` is the receiver a call must
 * pass, and without one the signature accepts any receiver. */
export function signature(scope: TermScope, parameters: readonly ts.ParameterDeclaration[],
    result: TypeNode | undefined, at: Node, span: Span,
    // A declared function's defaulted parameter may be omitted: `undefined`
    // is what a short call binds there. Function types have no defaults.
    declared: boolean = false): FunctionTerm[] {
  const forms = signatures(scope, parameters, result, at, span, declared);
  // A guard's promise is a second form beside the plain one; any other second
  // form is a rest over several tuples.
  const plain = forms.filter((f) => f.effect.promise === null);
  if (plain.length !== 1) return scope.fail(at, "a rest parameter over several tuples is several signatures");
  return forms;
}

/** A generic signature's binders and forms: its own type parameters are
 * binders, named by spelling, which shadow the enclosing ones. */
function quantified(scope: TermScope, typeParameters: readonly ts.TypeParameterDeclaration[],
    parameters: readonly ts.ParameterDeclaration[], result: TypeNode, at: Node, span: Span):
    Within<{ value: "any"; store: "grow" }, { binders: Extract<TypeTerm, { k: "scheme" }>["binders"]; forms: FunctionTerm[] }> {
  const own = typeParameters.map(p => p.name.text);
  const binders: Extract<TypeTerm, { k: "scheme" }>["binders"] = typeParameters.map(p => ({
    name: p.name.text, bound: null, resolution: null, default: null,
    span: spanOf(scope, p) }));
  const inner: TermScope = {
    ...scope,
    awaited: node => !(ts.isIdentifier(node.typeName) && own.includes(node.typeName.text)) &&
      (scope.awaited?.(node) ?? false),
    associatedAlias: node => ts.isIdentifier(node.typeName) && own.includes(node.typeName.text)
      ? null : scope.associatedAlias?.(node) ?? null,
    associated(input, span, node) {
      const binder = input.k === "binder" ? binders.find(b => b.name === input.name) : undefined;
      if (!binder) return scope.associated?.(input, span, node) ??
        scope.fail(node, "Awaited requires the input of a resolution-qualified parameter");
      if (binders.length !== 1) return scope.fail(node,
        "a resolution-qualified scheme has exactly one source parameter");
      binder.resolution ??= resolutionSlots(binder.name, "resolvable");
      if (binder.resolution.result === null) return scope.fail(node, "Awaited requires a resolvable parameter");
      return { k: "binder", name: binder.resolution.result, span };
    },
    named(node, span, read) {
      if (ts.isIdentifier(node.typeName) && own.includes(node.typeName.text)) {
        if (node.typeArguments?.length) scope.fail(node, "a type parameter takes no type arguments");
        return { k: "binder", name: node.typeName.text, span };
      }
      return scope.named(node, span, read);
    },
  };
  for (const [index, p] of typeParameters.entries()) {
    const binder = binders[index];
    if (!binder) return scope.fail(p, "missing type parameter");
    binder.bound = p.constraint ? typeTerm(inner, p.constraint, p) : null;
    binder.default = p.defaultType ? typeTerm(inner, p.defaultType, p) : null;
  }
  return { binders, forms: signatures(inner, parameters, result, at, span) };
}

/** A signature whose rest parameter is a union of tuples, `...[v]: [] | [T]`,
 * accepts each tuple's positions: it is one signature per tuple, all
 * returning its result, which a value meets by meeting every one. Such a
 * rest parameter may destructure its tuple only where the signature has no
 * body, so the pattern binds nothing the fragment reads. Any other signature
 * is exactly one. */
export function signatures(scope: TermScope, parameters: readonly ts.ParameterDeclaration[],
    result: TypeNode | undefined, at: Node, span: Span, declared: boolean = false,
    // A result the caller states instead of reading `result`, such as the
    // receiver a library overlay puts for a `this` result.
    given?: TypeTerm): Within<{ value: "any"; store: "grow" }, FunctionTerm[]> {
  const head = parameters[0];
  const stated = !!head && ts.isIdentifier(head.name) && head.name.text === "this";
  if (stated && (!head.type || head.questionToken || head.dotDotDotToken || head.initializer))
    scope.fail(head, "a receiver needs a required type annotation");
  const receiver = stated ? typeTerm(scope, head.type, head) : null;
  const ordinary = stated ? parameters.slice(1) : [...parameters];
  const optional = (p: ts.ParameterDeclaration) => !!p.questionToken || (declared && !!p.initializer);
  const firstOptional = ordinary.findIndex(optional);
  const params: TypeTerm[] = [];
  let rest: TypeTerm | null = null;
  let alternatives: TypeTerm[][] | null = null;
  for (const [index, p] of ordinary.entries()) {
    const pattern = !declared && !!p.dotDotDotToken && ts.isArrayBindingPattern(p.name);
    if (!(ts.isIdentifier(p.name) || pattern) || (ts.isIdentifier(p.name) && p.name.text === "this") ||
        (p.initializer && !declared))
      scope.fail(p, "expected an ordinary parameter");
    if (p.dotDotDotToken) {
      if (index !== ordinary.length - 1) scope.fail(p, "a rest parameter must be the last one");
      const type = restTerm(scope, typeTerm(scope, p.type, p));
      // A union of tuples is one signature per tuple.
      if (type.k === "union") {
        alternatives = type.parts.map(part => {
          const contract = restPositions(restTerm(scope, part));
          if (!contract || contract.k !== "positions") return scope.fail(p, restRefusal(part));
          return contract.positions;
        });
        continue;
      }
      // A rest typed by a type parameter is a pack parameter: the actuals
      // past the fixed ones are, as one list, at it. A declaration's own
      // parameter typing it inside the declaration is a packed one: its
      // instances are arrays or tuples, and the lists their elements form.
      if (type.k === "binder" || type.k === "parameter") {
        rest = { k: "pack", of: type, span: spanOf(scope, p) };
        continue;
      }
      // A tuple rest is a fixed number of further positions, which is how
      // TypeScript itself reads it, so the signature carries them. An array
      // rest is any number of them: the signature says what each one is.
      const contract = restPositions(type);
      if (!contract) scope.fail(p, restRefusal(type));
      if (contract.k === "positions") params.push(...contract.positions);
      else rest = contract.element;
    } else {
      if (!optional(p) && firstOptional >= 0 && index > firstOptional)
        scope.fail(p, "a required parameter cannot follow an optional one");
      const type = typeTerm(scope, p.type, p);
      params.push(optional(p) ? optionalTerm(type, spanOf(scope, p)) : type);
    }
  }
  // A result `Within<F, T>` states the signature's effect, `F`, of its
  // result `T` (`statedResult`).
  const statement = given ? { stated: null, result } : statedResult(scope, result, at);
  // A guard's result, `x is T` (`asserts x is T`), is its plain result,
  // `boolean` (`void`), and a promise about the parameter it names: a second
  // signature at the same parameters, its result the promise's type.
  const written = statement.result;
  const predicate = !given && written && ts.isTypePredicateNode(written)
    ? promiseOf(scope, written, ordinary) : null;
  const resultTerm = given ?? (predicate ? predicate.plain : typeTerm(scope, written, at));
  const effect = statement.stated ? statedEffect(statement.stated) : ordinaryEffect;
  const forms = (alternatives ?? [[]]).map((positions): FunctionTerm =>
    ({ k: "function", effect, receiver, params: [...params, ...positions], rest, result: resultTerm, span }));
  // A guard's statement bounds both signatures: they run the same code.
  return predicate
    ? [...forms, ...forms.map((f): FunctionTerm =>
        ({ ...f, effect: { ...effect, promise: predicate.effect.promise }, result: predicate.type }))]
    : forms;
}

/** Where `Within` may stand: the refusal of any other place. */
export const WITHIN_PLACE = "`Within` states a written signature's effect, at its result annotation only";

/** The call effect a statement gives its signature: its footprint and
 * on-throw flag, no promise, no fresh result, no receiver-store exception. */
export const statedEffect = (stated: StatedEffect): Within<{ value: "any"; store: "grow" }, CallEffect> =>
  ({ ...footprintEffect(stated.footprint), onThrow: stated.onThrow });

/** A result annotation's statement of its signature's effect,
 * `Within<F, T>` with `Within` the verifier's (SOURCE-ELABORATION.md,
 * "Stated effects"), and the result `T` it is stated of; no statement, and
 * the annotation itself, where the result is no such reference. `F` is a
 * type literal written in place, `{ value: "keep" | "any"; store: "keep" |
 * "grow" | "any" }`, with `onThrow: true` (or `onThrow?: true`) where the
 * footprint holds on a throw too. Refused: a statement of nothing, the
 * footprint letting everything change; one on an
 * async definition, whose throw is its promise's rejection; one on a
 * constructor or a construct signature, whose effect is its class's
 * construction. */
export function statedResult(scope: TermScope, result: TypeNode | undefined, at: Node | null):
    Within<{ value: "any"; store: "grow" }, { stated: StatedEffect | null; result: TypeNode | undefined }> {
  const unwrapped = result && unwrap(result);
  // A guard states its effect at its promise's type, `x is Within<F, T>`,
  // which TypeScript reads as `x is T`: the predicate stays the result.
  const predicate = unwrapped && ts.isTypePredicateNode(unwrapped) ? unwrapped : null;
  const node = predicate ? predicate.type && unwrap(predicate.type) : unwrapped;
  if (!node || !ts.isTypeReferenceNode(node) || !scope.stated?.(node)) return { stated: null, result };
  const [footprint, type, ...others] = node.typeArguments ?? [];
  if (!footprint || !type || others.length)
    return scope.fail(node, "`Within` takes a footprint and a result: `Within<F, T>`");
  if (at && (ts.isConstructorDeclaration(at) || ts.isConstructSignatureDeclaration(at) || ts.isConstructorTypeNode(at)))
    return scope.fail(node, "`Within` on a constructor is outside the fragment: its effect is its class's construction");
  if (at && (ts.isFunctionDeclaration(at) || ts.isMethodDeclaration(at) || ts.isArrowFunction(at) ||
      ts.isFunctionExpression(at)) && at.modifiers?.some(m => m.kind === ts.SyntaxKind.AsyncKeyword))
    return scope.fail(node, "`Within` on an async definition is outside the fragment: its call returns a promise where its body throws, so no footprint of its body's normal return is the call's");
  const stated = statementOf(scope, footprint);
  if (stated.footprint.value === "any" && stated.footprint.store === "any")
    return scope.fail(footprint, "`Within` letting every location change states nothing: a throw's heap is as unconstrained by it as a normal return's");
  return { stated, result: predicate ? result : type };
}

/** A guard's promised type as written, `T` of `x is T`, or of `x is
 * Within<F, T>`, whose statement `statedResult` reads. */
function promisedType(scope: TermScope, node: ts.TypePredicateNode): Within<{ value: "any"; store: "grow" }, TypeNode | undefined> {
  const written = node.type && unwrap(node.type);
  return written && ts.isTypeReferenceNode(written) && scope.stated?.(written) ? written.typeArguments?.[1] : node.type;
}

/** A statement's footprint, written in place as a type literal. */
function statementOf(scope: TermScope, written: TypeNode): Within<{ value: "any"; store: "grow" }, StatedEffect> {
  const node = unwrap(written);
  const shape = "a footprint is written in place as `{ value: \"keep\" | \"any\"; store: \"keep\" | \"grow\" | \"any\" }`, with `onThrow: true` where it holds on a throw too";
  if (!ts.isTypeLiteralNode(node)) return scope.fail(written, shape);
  let value: ClosedFootprint["value"] | null = null;
  let store: ClosedFootprint["store"] | null = null;
  let onThrow = false;
  const seen = new Set<string>();
  for (const member of node.members) {
    if (!ts.isPropertySignatureDeclaration(member) || !ts.isIdentifier(member.name) || member.modifiers?.length ||
        !member.type || seen.has(member.name.text))
      return scope.fail(member, shape);
    seen.add(member.name.text);
    const optional = member.postfixToken?.kind === ts.SyntaxKind.QuestionToken;
    const type = unwrap(member.type);
    const literal = ts.isLiteralTypeNode(type) ? type.literal : null;
    const text = literal && ts.isStringLiteral(literal) ? literal.text : null;
    if (member.name.text === "value" && !optional && (text === "keep" || text === "any")) value = text;
    else if (member.name.text === "store" && !optional && (text === "keep" || text === "grow" || text === "any"))
      store = text;
    else if (member.name.text === "onThrow" && literal?.kind === ts.SyntaxKind.TrueKeyword) onThrow = true;
    else return scope.fail(member, shape);
  }
  if (value === null || store === null) return scope.fail(written, shape);
  return { footprint: { value, store }, onThrow };
}

/** A type predicate's plain result, its effect and its promise's type: `x
 * is T` a type guard's, about the parameter `x`, `asserts x is T` an assertion
 * function's. Refused: a predicate about the receiver (`this is T`), whose
 * value is no actual; `asserts x` without a type, which promises the argument
 * truthy, no type of the fragment. */
export function promiseOf(scope: TermScope, node: ts.TypePredicateNode, ordinary: readonly ts.ParameterDeclaration[]):
    Within<{ value: "any"; store: "grow" }, { plain: TypeTerm; effect: CallEffect; type: TypeTerm }> {
  const name = node.parameterName;
  if (!ts.isIdentifier(name))
    return scope.fail(node, "a guard on `this` (`this is T`) is outside the fragment: its promise is about the receiver, which is no actual of the call");
  const promised = promisedType(scope, node);
  if (!promised)
    return scope.fail(node, "`asserts x` without a type is outside the fragment: it promises the argument truthy, which is no type of the fragment");
  const param = ordinary.findIndex((p) => ts.isIdentifier(p.name) && p.name.text === name.text);
  const declared = ordinary[param];
  if (!declared || declared.dotDotDotToken)
    return scope.fail(node, "a type predicate names a parameter other than a rest one");
  const span = spanOf(scope, node);
  return {
    plain: { k: "atom", name: node.assertsModifier ? "void" : "boolean", span },
    effect: promiseEffect(node.assertsModifier !== undefined, param),
    type: typeTerm(scope, promised, node),
  };
}

/** Several signatures as one term: their intersection, which a value meets by
 * meeting each. */
export function oneTerm(terms: FunctionTerm[], span: Span): Within<{ value: "any"; store: "grow" }, TypeTerm> {
  return terms.length === 1 && terms[0] ? terms[0] : { k: "intersection", parts: terms, span };
}

type SchemeTerm = Extract<TypeTerm, { k: "scheme" }>;

/** Overloads of one callee, some of them generic, as one term. Where none is
 * generic, their intersection (`oneTerm`). Otherwise one scheme over every
 * generic overload's binders, holding every overload's signatures: each
 * names only its own binders, so quantifying the others over it states the
 * same signature, and the scheme is the overloads' intersection. Two
 * generic overloads binding the same name are refused: a signature's binder
 * would be quantified at both. */
export function overloadTerm(terms: (FunctionTerm | SchemeTerm)[], span: Span, what: string):
    Within<{ value: "any"; store: "grow" }, TypeTerm> {
  const schemes = terms.filter((t): t is SchemeTerm => t.k === "scheme");
  if (!schemes.length) return oneTerm(terms.filter((t): t is FunctionTerm => t.k === "function"), span);
  const [only] = terms;
  if (terms.length === 1 && only) return only;
  const binders = schemes.flatMap(s => s.binders);
  const names = binders.map(b => b.name);
  if (new Set(names).size !== names.length)
    throw Error(`${what} selects generic overloads binding the same type parameter name`);
  return { k: "scheme", binders, signatures: terms.flatMap(t => t.k === "scheme" ? t.signatures : [t]), span };
}

/** A member's key: an identifier, a declaration's string literal, or a
 * computed `[x]` whose `x` the scope resolves to a `unique symbol` constant.
 * Anything else has no key here. */
function propertyKey(scope: TermScope, name: Node | undefined): Within<{ value: "any"; store: "grow" }, PropertyKey | null> {
  if (!name) return null;
  if (ts.isIdentifier(name) || (!scope.annotation && ts.isStringLiteral(name))) return name.text;
  // A numeric name is the property its value names, `ToString` of it:
  // `0x10`, `16` and `1_6` are the key "16".
  if (ts.isNumericLiteral(name)) return numericKey(name.text);
  if (ts.isComputedPropertyName(name) &&
      (ts.isIdentifier(name.expression) || ts.isPropertyAccessExpression(name.expression))) {
    const literal = scope.literalKey?.(name.expression);
    if (literal !== null && literal !== undefined) return literal;
    if (scope.symbol) return { symbol: scope.symbol(name.expression) };
  }
  if (ts.isPrivateIdentifier(name) && scope.privateName) return { symbol: scope.privateName(name) };
  return null;
}

/** A record, or an interface body when `methods` is set: its method
 * signatures read the containing declaration as their receiver. A type
 * literal nested in a declaration (`methods` is "nested") may state plain
 * methods, host-relative members as an interface's are; one optional or
 * generic has no declaration to be read in. */
export function members(scope: TermScope, list: readonly TypeElement[], at: Node, span: Span,
    methods: boolean | "nested"): Within<{ value: "any"; store: "grow" }, TypeTerm> {
  const fields: Extract<TypeTerm, { k: "object" }>["fields"] = [];
  let stringIndex: Extract<TypeTerm, { k: "object" }>["stringIndex"] = null;
  const calls: FunctionTerm[] = [];
  const names = new Set<string>();
  // Number index signatures, each subsumed by a string index of the same
  // contract or the object's number index once every member is read.
  type Index = NonNullable<Extract<TypeTerm, { k: "object" }>["stringIndex"]>;
  const numberIndexes: { member: Node; index: Index }[] = [];
  let symbolIndex: Index | null = null;
  const constructs: TypeTerm[] = [];
  // The fields property signatures state, which a class value's type states
  // as its static fields.
  const properties = new Set<Extract<TypeTerm, { k: "object" }>["fields"][number]>();
  const readonlyOnly = (modifiers: readonly Node[] | undefined) =>
    !modifiers?.some(m => m.kind !== ts.SyntaxKind.ReadonlyKeyword);
  const isReadonly = (modifiers: readonly Node[] | undefined) =>
    modifiers?.some(m => m.kind === ts.SyntaxKind.ReadonlyKeyword) === true;
  const named = (member: TypeElement & { name?: Node }, message: string): PropertyKey => {
    const key = propertyKey(scope, member.name) ?? scope.fail(member, message);
    const text = typeof key === "string" ? key : `[symbol ${key.symbol}]`;
    if (names.has(text)) scope.fail(member, "duplicate field name in a record");
    names.add(text);
    return key;
  };
  if (scope.annotation && !list.length) scope.fail(at, "a record with no field has no location");
  // An annotation's index signature is checked first, then its fields, and
  // only then is any other member refused.
  const ordered = scope.annotation
    ? [...list.filter(ts.isIndexSignatureDeclaration), ...list.filter(ts.isPropertySignatureDeclaration),
       ...list.filter(m => !ts.isIndexSignatureDeclaration(m) && !ts.isPropertySignatureDeclaration(m))]
    : list;
  for (const member of ordered) {
    const memberSpan = spanOf(scope, member);
    if (ts.isPropertySignatureDeclaration(member)) {
      // A `readonly` member is a read capability: its write contract is
      // `never`, and nothing else about the field changes. A member's `?` is
      // its postfix token: the field constrains its key only where the object
      // has it.
      const optional = member.postfixToken?.kind === ts.SyntaxKind.QuestionToken;
      const message = scope.annotation ? "expected a required mutable field" : "unsupported property signature";
      if (!readonlyOnly(member.modifiers) || !member.type)
        scope.fail(member, message);
      const name = named(member, message);
      const field = { name, optional, readonly: isReadonly(member.modifiers),
        type: typeTerm(scope, member.type, member), span: memberSpan };
      fields.push(field);
      properties.add(field);
    } else if (ts.isIndexSignatureDeclaration(member)) {
      const parameter = member.parameters[0];
      // A mutable index is a writable one at its read contract; Lean keeps
      // it invariant, as a mutable field is.
      if (member.parameters.length !== 1 || !parameter?.type || !member.type || !readonlyOnly(member.modifiers))
        scope.fail(member, "unsupported index signature");
      const kinds = indexKinds(scope, parameter.type);
      const index = { readonly: isReadonly(member.modifiers), value: typeTerm(scope, member.type, member),
        span: memberSpan };
      if (kinds.includes("string")) {
        if (stringIndex && !sameIndex(stringIndex, index))
          scope.fail(member, "two string index signatures with different contracts");
        stringIndex = index;
      }
      if (kinds.includes("number")) numberIndexes.push({ member, index });
      if (kinds.includes("symbol")) {
        if (symbolIndex && !sameIndex(symbolIndex, index))
          scope.fail(member, "two symbol index signatures with different contracts");
        symbolIndex = index;
      }
    } else if (ts.isConstructSignatureDeclaration(member)) {
      // A construct signature, read as a type literal's are
      // (`constructorForms`): the object is a class value.
      constructs.push(...constructorForms(scope, member, memberSpan));
    } else if (scope.annotation && !ts.isMethodSignatureDeclaration(member)) {
      scope.fail(at, "unsupported member in a record type");
    } else if (ts.isMethodSignatureDeclaration(member) && methods === true && member.typeParameters?.length &&
        !member.postfixToken && !member.modifiers?.length) {
      // A generic method is a readonly member whose type is a scheme: its own
      // type parameters are binders, named by spelling, which shadow the
      // declaration's. One whose signature is outside the fragment refuses
      // the declaration: the member is both read and produced at its
      // contract, and no weaker type is safe for both.
      const name = named(member, "unsupported method signature");
      if (!member.type) scope.fail(member, "unsupported method signature");
      const { binders, forms } = quantified(scope, member.typeParameters, member.parameters, member.type,
        member, memberSpan);
      if (forms.some(m => m.receiver)) scope.fail(member, GENERIC_METHOD_RECEIVER);
      fields.push({ name, optional: false, readonly: true,
        type: { k: "scheme", binders,
          signatures: forms.map(m => ({ ...m, receiver: { k: "self", span: memberSpan } })),
          span: memberSpan }, span: memberSpan });
    } else if (ts.isMethodSignatureDeclaration(member)) {
      if (!methods || !member.type || member.typeParameters?.length || member.modifiers?.length)
        scope.fail(member, "unsupported method signature");
      if (methods === "nested" && member.postfixToken)
        scope.fail(member, "an optional method of a nested type literal has no declaration as its receiver");
      const name = named(member, "unsupported method signature");
      const forms = signatures(scope, member.parameters, member.type, member, memberSpan);
      // An optional method, `return?(...)`, is an optional field, whose
      // function takes the declaration as receiver, never another.
      const optional = member.postfixToken?.kind === ts.SyntaxKind.QuestionToken;
      if (optional && forms.some(m => m.receiver))
        scope.fail(member, "an optional method with a `this` parameter is outside the fragment: an optional method is an optional field, whose function takes its declaration as receiver");
      fields.push({ name, optional, readonly: false,
        type: oneTerm(forms.map(m => ({ ...m, receiver: hostReceiver(m, memberSpan) })), memberSpan),
        span: memberSpan });
    } else if (ts.isCallSignatureDeclaration(member)) {
      if (member.typeParameters?.length || !member.type)
        scope.fail(member, "generic or incomplete call signature");
      calls.push(...signatures(scope, member.parameters, member.type, member, memberSpan));
    } else scope.fail(member, "unsupported object member");
  }
  // Every numeric key is a string key: a number index with the string
  // index's contract adds nothing. One with another contract constrains the
  // canonical numeric keys apart from the others: the object's number index.
  let numberIndex: Index | null = null;
  for (const { member, index } of numberIndexes) {
    if (stringIndex && sameIndex(stringIndex, index)) continue;
    if (numberIndex && !sameIndex(numberIndex, index))
      scope.fail(member, "two number index signatures with different contracts");
    numberIndex = index;
  }
  // An interface of construct signatures alone is a class value meeting
  // each, as such a type literal is. With properties beside one construct
  // signature, it is a class value holding them as its static fields, own
  // data properties under invariant contracts.
  if (constructs.length) {
    const [only] = constructs;
    if (!fields.length && !stringIndex && !numberIndex && !symbolIndex && !calls.length)
      return constructs.length === 1 && only ? only : { k: "intersection", parts: constructs, span };
    if (stringIndex || numberIndex || symbolIndex || calls.length || constructs.length !== 1 ||
        only?.k !== "constructor" || fields.some(f => !properties.has(f)))
      scope.fail(at, "an object type with construct signatures and members other than properties: a class " +
        "value's type states its construct signature and its static fields, data properties");
    const statics = fields.map(f => !f.optional
      ? { name: f.name, type: f.type, ...(f.readonly ? { readonly: true as const } : {}) }
      : scope.fail(at, "an object type with construct signatures and an optional property: a class value's " +
        "static fields are required data properties"));
    return { ...only, statics };
  }
  return { k: "object", fields, stringIndex, ...(numberIndex ? { numberIndex } : {}),
    ...(symbolIndex ? { symbolIndex } : {}), calls, span };
}

/** Whether two index signatures state the same contract. */
function sameIndex(a: { readonly: boolean; value: TypeTerm }, b: { readonly: boolean; value: TypeTerm }): Within<{ value: "keep"; store: "keep" }, boolean> {
  return a.readonly === b.readonly && sameTerm(a.value, b.value);
}

/** Whether two type terms state the same contract: equal field by field,
 * each `span` left out, an absent optional field equal only to an absent
 * one. */
function sameTerm(a: TypeTerm, b: TypeTerm): Within<{ value: "keep"; store: "keep" }, boolean> {
  switch (a.k) {
    case "atom": return b.k === "atom" && a.name === b.name;
    case "literal": return b.k === "literal" && a.name === b.name && a.text === b.text;
    case "unique": return b.k === "unique" && a.symbol === b.symbol;
    case "union": return b.k === "union" && sameTerms(a.parts, b.parts);
    case "intersection": return b.k === "intersection" && sameTerms(a.parts, b.parts);
    case "array":
      return b.k === "array" && a.presence === b.presence && a.readonly === b.readonly && sameTerm(a.element, b.element);
    case "tuple":
      return b.k === "tuple" && a.presence === b.presence && a.readonly === b.readonly &&
        sameTerms(a.required, b.required) && sameTerms(a.optional, b.optional) && sameOptionalTerm(a.rest, b.rest);
    case "object":
      return b.k === "object" && a.fields.length === b.fields.length && a.fields.every((f, i) => {
        const g = b.fields[i];
        return g !== undefined && sameKey(f.name, g.name) && f.optional === g.optional && f.readonly === g.readonly &&
          sameTerm(f.type, g.type);
      }) && sameOptionalIndex(a.stringIndex, b.stringIndex) &&
        sameOptionalIndex(a.numberIndex ?? null, b.numberIndex ?? null) &&
        sameOptionalIndex(a.symbolIndex ?? null, b.symbolIndex ?? null) && sameTerms(a.calls, b.calls) &&
        sameOptionalTerm(a.prototype ?? null, b.prototype ?? null) && a.host === b.host &&
        sameStrings(a.stable ?? null, b.stable ?? null);
    case "function":
      return b.k === "function" && sameEffect(a.effect, b.effect) && sameOptionalTerm(a.receiver, b.receiver) &&
        sameTerms(a.params, b.params) && sameOptionalTerm(a.rest, b.rest) && sameTerm(a.result, b.result);
    case "constructor":
      return b.k === "constructor" && sameEffect(a.effect, b.effect) && sameTerms(a.params, b.params) &&
        sameOptionalTerm(a.rest, b.rest) && sameTerm(a.result, b.result) && sameStatics(a.statics ?? null, b.statics ?? null);
    case "pack": return b.k === "pack" && sameTerm(a.of, b.of);
    case "scheme":
      return b.k === "scheme" && a.binders.length === b.binders.length && a.binders.every((x, i) => {
        const y = b.binders[i];
        return y !== undefined && x.name === y.name && sameOptionalTerm(x.bound, y.bound) &&
          sameSlots(x.resolution, y.resolution) && sameOptionalTerm(x.default, y.default);
      }) && sameTerms(a.signatures, b.signatures);
    case "callable": return b.k === "callable";
    case "self": return b.k === "self";
    case "parameter": return b.k === "parameter" && a.index === b.index;
    case "binder": return b.k === "binder" && a.name === b.name;
    case "reference":
      return b.k === "reference" && a.reference.name === b.reference.name &&
        a.reference.arguments.length === b.reference.arguments.length &&
        a.reference.arguments.every(([start, end], i) => {
          const other = b.reference.arguments[i];
          return other !== undefined && other[0] === start && other[1] === end;
        }) &&
        a.reference.target.module === b.reference.target.module && a.reference.target.name === b.reference.target.name &&
        sameTerms(a.args, b.args);
  }
}

/** Whether two lists of type terms are equal element by element. */
function sameTerms(a: readonly TypeTerm[], b: readonly TypeTerm[]): Within<{ value: "keep"; store: "keep" }, boolean> {
  return a.length === b.length && a.every((x, i) => {
    const y = b[i];
    return y !== undefined && sameTerm(x, y);
  });
}

/** Whether two type terms, each possibly absent, are equal. */
function sameOptionalTerm(a: TypeTerm | null, b: TypeTerm | null): Within<{ value: "keep"; store: "keep" }, boolean> {
  return a === null || b === null ? a === b : sameTerm(a, b);
}

/** Whether two index signatures, each possibly absent, state the same contract. */
function sameOptionalIndex(a: { readonly: boolean; value: TypeTerm } | null, b: { readonly: boolean; value: TypeTerm } | null): Within<{ value: "keep"; store: "keep" }, boolean> {
  return a === null || b === null ? a === b : sameIndex(a, b);
}

/** Whether two property keys are the same key. */
function sameKey(a: PropertyKey, b: PropertyKey): Within<{ value: "keep"; store: "keep" }, boolean> {
  return typeof a === "string" || typeof b === "string" ? a === b : a.symbol === b.symbol;
}

/** Whether two lists of strings, each possibly absent, are equal. */
function sameStrings(a: readonly string[] | null, b: readonly string[] | null): Within<{ value: "keep"; store: "keep" }, boolean> {
  return a === null || b === null ? a === b : a.length === b.length && a.every((x, i) => x === b[i]);
}

/** Whether two class values' static fields, each list possibly absent, are equal. */
function sameStatics(a: readonly { name: PropertyKey; type: TypeTerm; readonly?: true }[] | null,
  b: readonly { name: PropertyKey; type: TypeTerm; readonly?: true }[] | null): Within<{ value: "keep"; store: "keep" }, boolean> {
  if (a === null || b === null) return a === b;
  return a.length === b.length && a.every((x, i) => {
    const y = b[i];
    return y !== undefined && sameKey(x.name, y.name) && sameTerm(x.type, y.type) && (x.readonly === true) === (y.readonly === true);
  });
}

/** Whether two resolution slots, each possibly absent, are equal. */
function sameSlots(a: ResolutionSlots | null, b: ResolutionSlots | null): Within<{ value: "keep"; store: "keep" }, boolean> {
  return a === null || b === null ? a === b : a.observation === b.observation && a.result === b.result;
}

/** Whether two call effects are equal; a promise, data of one key, by its
 * JSON text. */
function sameEffect(a: CallEffect, b: CallEffect): Within<{ value: "keep"; store: "keep" }, boolean> {
  return a.footprint.value === b.footprint.value && a.footprint.store === b.footprint.store &&
    a.fresh === b.fresh && a.receiverStore === b.receiverStore && a.onThrow === b.onThrow &&
    a.receiverOwn === b.receiverOwn && a.freshObject === b.freshObject &&
    JSON.stringify(a.requires) === JSON.stringify(b.requires) &&
    JSON.stringify(a.elements) === JSON.stringify(b.elements) &&
    (a.promise === null || b.promise === null ? a.promise === b.promise : samePromise(a.promise, b.promise));
}

/** Whether two call promises are about the same parameter, both guards or
 * both assertions. */
function samePromise(a: CallPromise, b: CallPromise): Within<{ value: "keep"; store: "keep" }, boolean> {
  if (a.guards !== undefined) return b.guards !== undefined && a.guards.param === b.guards.param;
  return b.asserts !== undefined && a.asserts.param === b.asserts.param;
}

/** The key kinds an index signature's parameter type names: `string`,
 * `number`, `symbol`, or a union of them. */
function indexKinds(scope: TermScope, node: TypeNode): Within<{ value: "any"; store: "grow" }, ("string" | "number" | "symbol")[]> {
  const kinds: ("string" | "number" | "symbol")[] = [];
  const add = (t: TypeTerm): void => {
    if (t.k === "union") t.parts.forEach(add);
    else if (t.k === "atom" && (t.name === "string" || t.name === "number" || t.name === "symbol")) kinds.push(t.name);
    else scope.fail(node, "an index signature's key is string, number or symbol");
  };
  add(scope.keys?.(node) ?? typeTerm(scope, node));
  return kinds;
}

/** `public`, `private` and `protected` are TypeScript's alone: at run time
 * the member is an ordinary property, so a class states it as any other
 * member. (`#x` names a private slot, not a property: it has no plain name.) */
export const CLASS_ACCESS: ts.SyntaxKind[] = [ts.SyntaxKind.PublicKeyword, ts.SyntaxKind.PrivateKeyword,
  ts.SyntaxKind.ProtectedKeyword];

/** A class declaration's instance type: its fields at their annotations and
 * its methods as readonly fields whose receiver is the instance. An instance
 * reaches a method through the prototype; within the fragment nothing tells a
 * prototype member from an own one, and no write reaches either, so the
 * readonly field is exact. Construction is the class value's concern. */
export function classInstance(scope: TermScope, node: ts.ClassDeclaration, span: Span,
    admit: (member: ts.ClassElement) => boolean = () => true): TypeTerm {
  const fields: Extract<TypeTerm, { k: "object" }>["fields"] = [];
  const names = new Set<string>();
  const ambient = node.modifiers?.some(m => m.kind === ts.SyntaxKind.DeclareKeyword) === true;
  // The field of an ambient class's bodyless method, by name: a later
  // overload of the name joins it, and the joined field takes the first's
  // place in the instance's fields. Member names are distinct (`named`), so
  // the name finds the one field it replaces.
  const overloads = new Map<string, Extract<TypeTerm, { k: "object" }>["fields"][number]>();
  const named = (member: ts.ClassElement & { name?: Node }): PropertyKey => {
    const name = member.name;
    // A private name `#x` is a key of its own, a symbol no code outside the
    // class spells (SOURCE-CONTRACTS.md, "Classes").
    const key = name && (ts.isIdentifier(name) || ts.isComputedPropertyName(name) || ts.isPrivateIdentifier(name))
      ? propertyKey(scope, name) : null;
    if (key === null) return scope.fail(member, "a class member needs a plain name");
    const text = typeof key === "string" ? key : `[symbol ${key.symbol}]`;
    if (names.has(text)) scope.fail(member, "duplicate class member");
    names.add(text);
    return key;
  };
  const only = (member: ts.ClassElement, allowed: ts.SyntaxKind[]) => {
    const modifiers = childrenOf(member, "modifiers");
    if (modifiers.some(m => !allowed.includes(m.kind) && !CLASS_ACCESS.includes(m.kind)))
      scope.fail(member, "a class member modifier outside the fragment");
  };
  for (const member of node.members) {
    if (!admit(member)) continue;
    const memberSpan = spanOf(scope, member);
    // A static member is the class value's, not an instance's.
    if ((ts.isPropertyDeclaration(member) || ts.isMethodDeclaration(member)) &&
        member.modifiers?.some(m => m.kind === ts.SyntaxKind.StaticKeyword))
      continue;
    // A static block is code the definition runs, no member of an instance.
    if (ts.isClassStaticBlockDeclaration(member)) continue;
    if (ts.isPropertyDeclaration(member)) {
      only(member, [ts.SyntaxKind.ReadonlyKeyword]);
      // `x?: T` is the optional field `x?: T | undefined` TypeScript
      // declares, as an optional parameter property is: a class field is
      // defined on every instance its construction allocates, holding
      // `undefined` where no initializer or constructor assigns it, and the
      // exact reading of `f?: T` (absent or a `T`) is false of it. `x!: T`
      // is a required one, whatever TypeScript was promised: the class
      // value's construction decides whether every instance holds a `T`
      // there.
      const name = named(member);
      const optional = member.postfixToken?.kind === ts.SyntaxKind.QuestionToken;
      // A field an ambient class declares without a type is read at
      // `unknown` and never written: nothing here says what it holds, or
      // what the code outside expects of it.
      const untyped = !member.type &&
        node.modifiers?.some(m => m.kind === ts.SyntaxKind.DeclareKeyword) === true;
      const declared = (): TypeTerm => typeTerm(scope, member.type, member);
      fields.push({ name, optional,
        readonly: untyped || member.modifiers?.some(m => m.kind === ts.SyntaxKind.ReadonlyKeyword) === true,
        type: untyped ? { k: "atom", name: "unknown", span: memberSpan }
          : optional ? optionalTerm(declared(), memberSpan) : declared(),
        span: memberSpan });
    } else if (ts.isMethodDeclaration(member)) {
      // An async method is one returning its promise: its annotation, which
      // its body, read with `await` and its returns as intrinsic steps, is
      // checked against.
      only(member, [ts.SyntaxKind.AsyncKeyword]);
      if (member.postfixToken || member.asteriskToken)
        scope.fail(member, "an optional or generator method is outside the fragment");
      // Overloads of an ambient class's method, several declarations of one
      // name without a body, are one member: the conjunction of their
      // signatures, as a declared function's overloads are (`oneTerm`). A
      // later overload joins the field the first one states.
      const overloadName = ambient && !member.body && !member.typeParameters?.length && ts.isIdentifier(member.name)
        ? member.name.text : undefined;
      const overload = overloadName === undefined ? undefined : overloads.get(overloadName);
      if (overload) {
        const forms = signature(scope, member.parameters, member.type, member, memberSpan, true);
        const added = forms.map((f) => ({ ...f, receiver: hostReceiver(f, memberSpan) }));
        const earlier = overload.type.k === "intersection"
          ? overload.type.parts.filter((p): p is FunctionTerm => p.k === "function")
          : overload.type.k === "function" ? [overload.type] : [];
        const joined = { ...overload, type: oneTerm([...earlier, ...added], overload.span) };
        overloads.set(overloadName ?? "", joined);
        continue;
      }
      const name = named(member);
      if (member.typeParameters?.length) {
        // A generic method is a host-relative member with quantified
        // signatures, as an interface's is: its own type parameters are
        // binders, named by spelling, which shadow the class's; its scheme's
        // signatures take the instance as receiver.
        const own = member.typeParameters.map(p => p.name.text);
        const inner: TermScope = {
          ...scope,
          named(node, span, read) {
            if (ts.isIdentifier(node.typeName) && own.includes(node.typeName.text)) {
              if (node.typeArguments?.length) scope.fail(node, "a type parameter takes no type arguments");
              return { k: "binder", name: node.typeName.text, span };
            }
            return scope.named(node, span, read);
          },
        };
        const binders = member.typeParameters.map(p => ({
          name: p.name.text,
    resolution: null,
          bound: p.constraint ? typeTerm(inner, p.constraint, p) : null,
          default: p.defaultType ? typeTerm(inner, p.defaultType, p) : null,
          span: spanOf(scope, p),
        }));
        // A defaulted parameter may be omitted, as a declared function's.
        const forms = signature(inner, member.parameters, member.type, member, memberSpan, true);
        if (forms.some((f) => f.receiver)) scope.fail(member, GENERIC_METHOD_RECEIVER);
        fields.push({ name, optional: false, readonly: true,
          type: { k: "scheme", binders, signatures: forms.map((f) => ({ ...f, receiver: { k: "self", span: memberSpan } })),
            span: memberSpan }, span: memberSpan });
        continue;
      }
      const forms = signature(scope, member.parameters, member.type, member, memberSpan, true);
      const field = { name, optional: false, readonly: true,
        type: oneTerm(forms.map((f) => ({ ...f, receiver: hostReceiver(f, memberSpan) })), memberSpan), span: memberSpan };
      fields.push(field);
      if (ambient && !member.body && typeof name === "string") overloads.set(name, field);
    } else if (ts.isConstructorDeclaration(member)) {
      // A parameter property is a field the constructor assigns from its
      // parameter. Its visibility is TypeScript's alone; `readonly` is the
      // field's. An optional one, `x?: T`, is the optional field
      // `x?: T | undefined` TypeScript declares: the constructor assigns it on
      // every call, with the `undefined` an omitted argument binds.
      for (const p of member.parameters) {
        if (!p.modifiers?.length) continue;
        if (!ts.isIdentifier(p.name) || p.dotDotDotToken)
          scope.fail(p, "a parameter property needs a plain parameter");
        const name = p.name.text;
        if (names.has(name)) scope.fail(p, "duplicate class member");
        names.add(name);
        const type = typeTerm(scope, p.type, p);
        fields.push({ name, optional: !!p.questionToken,
          readonly: p.modifiers.some(m => m.kind === ts.SyntaxKind.ReadonlyKeyword),
          type: p.questionToken ? optionalTerm(type, spanOf(scope, p)) : type, span: spanOf(scope, p) });
      }
    } else if (!ts.isSemicolonClassElement(member)) {
      scope.fail(member, classMemberRefusal(member));
    }
  }
  const joined = fields.map((f) => typeof f.name === "string" ? overloads.get(f.name) ?? f : f);
  return { k: "object", fields: joined, stringIndex: null, calls: [], span };
}
