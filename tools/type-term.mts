/** The one reading of TypeScript type syntax as a source type term. Function
 * annotations and declaration bodies share it: what differs between them is
 * where a name resolves, which the caller's scope decides, and which record
 * forms an annotation may state. */
import * as ts from "typescript/unstable/ast";
import type { Identifier, Node, SourceFile, TypeAliasDeclaration, TypeElement, TypeNode, TypeReferenceNode } from "typescript/unstable/ast";
import type { Span } from "./span.mts";
import { childrenOf } from "./syntax.mts";
import type { PropertyKey, ResolutionSlots, TypeTerm } from "./declaration-types.mts";

/** The projections a qualified parameter owns: an awaitable one its
 * observation, a resolvable one also its result. */
export function resolutionSlots(name: string, qualification: "resolvable"): ResolutionSlots & { result: string };
export function resolutionSlots(name: string, qualification: "awaitable" | "resolvable"): ResolutionSlots;
export function resolutionSlots(name: string, qualification: "awaitable" | "resolvable"): ResolutionSlots {
  return { observation: `#observe:${name}`, result: qualification === "resolvable" ? `#resolve:${name}` : null };
}

/** The names a qualified parameter's projections own. */
const ownedSlots = (slots: ResolutionSlots | null): string[] =>
  slots ? [slots.observation, ...(slots.result === null ? [] : [slots.result])] : [];

// Numeric literals in the fragment are plain decimals; every other spelling
// (hex, binary, octal, separators) is outside it. A bigint literal is read as
// its integer, whatever its spelling (`bigintText`).
const DECIMAL = /^[0-9]+(\.[0-9]+)?([eE][+-]?[0-9]+)?$/;

/** Visit every source type constructor, with the generic method binders in scope.
 * Readers use the same walk for annotation admissibility and name checking. */
export function visitType(term: TypeTerm, visit: (term: TypeTerm, bound: ReadonlySet<string>) => void,
    bound: ReadonlySet<string> = new Set()): void {
  visit(term, bound);
  const go = (part: TypeTerm): void => visitType(part, visit, bound);
  switch (term.k) {
    case "atom": case "literal": case "unique": case "callable": case "self": case "parameter": case "binder": return;
    case "union": case "intersection": term.parts.forEach(go); return;
    case "array": go(term.element); return;
    case "tuple":
      term.required.forEach(go); term.optional.forEach(go); if (term.rest) go(term.rest); return;
    case "object":
      term.fields.forEach(field => go(field.type)); term.calls.forEach(go);
      if (term.stringIndex) go(term.stringIndex.value);
      if (term.numberIndex) go(term.numberIndex.value);
      if (term.symbolIndex) go(term.symbolIndex.value);
      if (term.prototype) go(term.prototype);
      return;
    case "function": if (term.receiver) go(term.receiver);
      term.params.forEach(go); if (term.rest) go(term.rest); go(term.result); return;
    case "constructor":
      term.params.forEach(go); if (term.rest) go(term.rest); go(term.result); return;
    case "pack": go(term.of); return;
    case "reference": term.args.forEach(go); return;
    case "scheme": {
      const inner = new Set([...bound, ...term.binders.flatMap(binder => [binder.name,
        ...ownedSlots(binder.resolution)])]);
      const scoped = (part: TypeTerm): void => visitType(part, visit, inner);
      term.binders.forEach(binder => {
        if (binder.bound) scoped(binder.bound);
        if (binder.default) scoped(binder.default);
      });
      term.signatures.forEach(scoped); return;
    }
    default: { const exhaustive: never = term; return exhaustive; }
  }
}

/** Admissibility of a source annotation, independent of its input representation. */
export function validateAnnotation(term: TypeTerm, fail: (span: Span, message: string) => never): void {
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
export function numericLexeme(node: ts.NumericLiteral, source: SourceFile): string | null {
  if (DECIMAL.test(node.text)) return node.text;
  const written = source.getFullText().slice(node.getStart(source), node.end).replace(/_/g, "");
  return node.text === "Infinity" && DECIMAL.test(written) ? written : null;
}

/** A bigint literal's value as its canonical decimal integer: `0x10n`, `1_0n`
 * and `16n` are all `16`. */
export function bigintText(literal: string, negative: boolean): string {
  const value = BigInt(literal.slice(0, -1).replace(/_/g, ""));
  return String(negative ? -value : value);
}

/** `{}`, an object type with no member: it constrains no key, and is every
 * value but `null` and `undefined`, a primitive included, not an empty
 * record. */
function emptyObject(span: Span): TypeTerm {
  return { k: "union", span, parts: (["boolean", "number", "string", "bigint", "symbol", "object"] as const)
    .map(name => ({ k: "atom", name, span })) };
}

/** The property key a numeric literal names: `ToString` of its value, as
 * JavaScript converts it. */
export function numericKey(literal: string): string {
  return String(Number(literal.replace(/_/g, "")));
}

/** A generic method declaring `this: T`. A generic method's member is a
 * scheme its member bound to the host meets whatever receiver the bound
 * function is given (DESIGN.md, "Method members are host-relative"), which
 * states no type the host must meet. */
export const GENERIC_METHOD_RECEIVER =
  "a generic method with a `this` parameter is outside the fragment: its member is a scheme the member bound to its host meets, which states no type the host must meet";

/** A method form's receiver: the declaration it is a member of, its host,
 * met with the type a `this` parameter states, which the host must meet. */
function hostReceiver(form: FunctionTerm, span: Span): TypeTerm {
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
export const REST_PACK_VALUE =
  `${REST_CONTRACT}: a type parameter typing a rest parameter and anything else would make the array a call ` +
  "collects a value of it, which it is not: the array is fresh, with the actuals and none of the " +
  "parameter's other members (at `string[] & { tag: string }` it has no `tag`)";

/** A module function's rest typed by its own type parameter whose bound is
 * no array or tuple of required positions written as one. */
export const REST_PACK_BOUND =
  `${REST_CONTRACT}: one typed by a type parameter collects the array its bound states, which must be ` +
  "written as an array or a tuple of required positions";

/** A rest parameter's type, a declared alias read through its equation at
 * the reference's arguments, as TypeScript reads one: the array a call
 * collects is viewed at that equation. */
export function restTerm(scope: TermScope, type: TypeTerm): TypeTerm {
  for (let seen = 0; type.k === "reference" && seen < 16; seen++) {
    const equation = scope.equation?.(type);
    if (!equation) break;
    type = equation;
  }
  return type;
}

/** Why a rest parameter's type is no contract for the array a call
 * collects, by its form. */
export function restRefusal(type: TypeTerm): string {
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
  named(node: TypeReferenceNode, span: Span, read: (node: TypeNode) => TypeTerm): TypeTerm;
  /** The resolved standard-library Awaited alias. Its associated projection
   * is read only through the enclosing descriptor scope. */
  awaited?(node: TypeReferenceNode): boolean;
  associated?(input: TypeTerm, span: Span, node: TypeReferenceNode): TypeTerm;
  /** A resolved associated-result alias expanded in this lexical scope. */
  associatedAlias?(node: TypeReferenceNode): TypeAliasDeclaration | null;
  expandingAliases?: ReadonlySet<TypeAliasDeclaration>;
  /** An annotation states records as the source fragment always has: named,
   * required fields and at most one readonly string index. A declaration body
   * states what its equation says, and Lean decides what lowers. */
  annotation: boolean;
  /** A declaration's own equation, when it is a type literal: its methods'
   * receiver is the declaration, as an interface's are. */
  body?: TypeNode;
  /** A computed key `[x]` or `[o.x]`: the index of the `unique symbol`
   * constant or readonly property it denotes. A scope without it reads no
   * symbol key. */
  symbol?(name: Identifier | ts.PropertyAccessExpression): number;
  /** A computed key `[x]` or `[o.x]` naming an entity of a string or number
   * literal type, as an enum member or a constant is: the key its value
   * names; null for any other. */
  literalKey?(name: Identifier | ts.PropertyAccessExpression): string | null;
  /** A class member's private name `#x`: the index of the symbol the
   * declaration document lists for it, a key no code outside the class
   * spells. A scope without it reads no private name. */
  privateName?(name: ts.PrivateIdentifier): number;
  /** `E.A` and `typeof E` for one of the file's enums: the member's literal
   * type and the enum's object type (PROGRAM-TYPING.md, "Enums"); null for any other
   * such node. A scope without it reads neither. */
  enumerated?(node: TypeNode, span: Span): TypeTerm | null;
  /** A type TypeScript computes from other types (`COMPUTED`): `typeof x`,
   * `keyof T`, `T[K]`, a template literal type. The scope evaluates it to the
   * equivalent type the fragment states, or refuses it with the reason; `read`
   * reads an operand in this scope. A scope without it reads none. */
  computed?(node: TypeNode, span: Span, read: (node: TypeNode) => TypeTerm): TypeTerm;
  /** A mapped type's keys, or a library mapped type's key argument
   * (`Record<K, V>`), as the union of literals and primitives TypeScript
   * computes for it, `"a" | "b"` for an alias of those, or null. A scope
   * without it reads the keys as written. */
  keys?(node: TypeNode): TypeTerm | null;
  /** A reference to a declared type alias of an array, a tuple or another
   * alias: its equation at the reference's arguments, or null. A scope
   * without it reads no rest parameter through an alias. */
  equation?(reference: Extract<TypeTerm, { k: "reference" }>): TypeTerm | null;
};

/** The type forms TypeScript computes from other types, as the syntax kind a
 * refusal names. Their meaning is the type TypeScript computes, which the
 * declaration reader evaluates (PROGRAM-TYPING.md, "Computed types"). */
export function computedForm(node: TypeNode): string | null {
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
 * or is an application of another such alias: over its parameters it is
 * known only at an application, so it has no equation of its own, and each
 * reference to it is a computed type, evaluated at the reference's arguments
 * (`computed-types.mts`). `aliasOf` is the alias a reference names, if any. */
export function computedAlias(node: Node, aliasOf: (reference: TypeReferenceNode) => TypeAliasDeclaration | null,
    seen: Set<Node> = new Set()): node is TypeAliasDeclaration {
  if (!ts.isTypeAliasDeclaration(node) || !node.typeParameters?.length || seen.has(node)) return false;
  seen.add(node);
  const body = unwrap(node.type);
  if (computedForm(body) !== null) return true;
  if (!ts.isTypeReferenceNode(body)) return false;
  const target = aliasOf(body);
  return !!target && computedAlias(target, aliasOf, seen);
}

const PRIMITIVE_KEYWORDS: ts.SyntaxKind[] = [ts.SyntaxKind.NullKeyword, ts.SyntaxKind.UndefinedKeyword,
  ts.SyntaxKind.BooleanKeyword, ts.SyntaxKind.NumberKeyword, ts.SyntaxKind.StringKeyword,
  ts.SyntaxKind.BigIntKeyword, ts.SyntaxKind.SymbolKeyword, ts.SyntaxKind.VoidKeyword];

/** An intersection's operands, nested intersections and parentheses flattened. */
function intersectionOperands(node: ts.IntersectionTypeNode): TypeNode[] {
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

const spanOf = (scope: TermScope, node: Node): Span => [node.getStart(scope.source), node.end];

const unwrap = (node: TypeNode): TypeNode => {
  while (ts.isParenthesizedTypeNode(node)) node = node.type;
  return node;
};

/** `x?: T` is `T | undefined` where the parameter is read: `undefined` is the
 * value bound when a call omits that position. */
export function optionalTerm(type: TypeTerm, span: Span): TypeTerm {
  return { k: "union", parts: [type, { k: "atom", name: "undefined", span }], span };
}

/** The rest parameter's contract as positions of the signature: a tuple of
 * required positions is a fixed number of further arguments, an array, mutable
 * or readonly, any number of them. Anything else has no reading as a
 * signature. */
export function restPositions(type: TypeTerm): { positions: TypeTerm[] } | { element: TypeTerm } | null {
  // The array a call collects is fresh: it is an array of its element, and
  // viewing it as `readonly` gives up only writes.
  if (type.k === "array") return { element: type.element };
  if (type.k === "tuple" && !type.optional.length && type.rest === null)
    return { positions: type.required };
  return null;
}

export function typeTerm(scope: TermScope, node: TypeNode | undefined, at: Node | null = null): TypeTerm {
  const term = readTypeTerm(scope, node, at);
  const location = node ?? at;
  if (scope.annotation && location)
    validateAnnotation(term, (_span, message) => scope.fail(location, message));
  return term;
}

function readTypeTerm(scope: TermScope, node: TypeNode | undefined, at: Node | null): TypeTerm {
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
      if (!scope.annotation) return atom("unknown");
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
  if (ts.isMappedTypeNode(node)) return expandMapped(mapped(scope, node), span, message => scope.fail(node, message));
  if (ts.isFunctionTypeNode(node)) {
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
    const forms = constructorForms(scope, node, span);
    const [only] = forms;
    return forms.length === 1 && only ? only : { k: "intersection", parts: forms, span };
  }
  if ((ts.isTypeReferenceNode(node) && node.typeName.kind !== ts.SyntaxKind.Identifier) || ts.isTypeQueryNode(node)) {
    const enumerated = scope.enumerated?.(node, span);
    if (enumerated) return enumerated;
  }
  if (ts.isTypeReferenceNode(node)) {
    if (node.typeName.kind !== ts.SyntaxKind.Identifier)
      return scope.fail(node, "type reference outside the fragment");
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
  // `x is T` and `asserts x is T` promise a relation between an argument and
  // the result or the completion, which no function type states: a caller
  // narrowing by one needs a fact tying the call's result to its argument.
  if (ts.isTypePredicateNode(node))
    return scope.fail(node, node.assertsModifier
      ? "an assertion function (`asserts x is T`) is outside the fragment: its promise, that a normal completion leaves the argument a `T`, relates the completion to the argument, which no function type states"
      : "a user-defined type guard (`x is T`) is outside the fragment: its promise, that a `true` result leaves the argument a `T`, relates the result to the argument, which no function type states");
  return scope.fail(node, `type outside the fragment (${ts.SyntaxKind[node.kind]})`);
}

/** A construct signature's forms, one per accepted argument list: it has no
 * receiver, and its rest, if any, is a function's. */
function constructorForms(scope: TermScope, node: ts.ConstructorTypeNode | ts.ConstructSignatureDeclaration,
    span: Span): TypeTerm[] {
  if (ts.isConstructorTypeNode(node) && node.modifiers?.length)
    scope.fail(node, "an abstract constructor type is outside the fragment");
  if (!node.type) scope.fail(node, "a constructor type needs its result type");
  const construct = (f: FunctionTerm): Extract<TypeTerm, { k: "constructor" }> => {
    if (f.receiver) scope.fail(node, "a constructor type has no receiver");
    return { k: "constructor", params: f.params, rest: f.rest, result: f.result, span };
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
 * the key and value terms as read, and its modifiers. A `-` modifier removes
 * what a homomorphic mapped type would copy from its source; over a key union
 * nothing is copied, so it states nothing. */
export type Mapped = { key: TypeTerm; value: TypeTerm; optional: boolean; readonly: boolean };

export function mapped(scope: TermScope, node: ts.MappedTypeNode): Mapped {
  if (node.nameType) scope.fail(node, "a mapped type with an 'as' clause is outside the fragment");
  if (node.members?.length) scope.fail(node, "a mapped type with members is outside the fragment");
  const parameter = node.typeParameter;
  const name = parameter.name.text;
  const names = (t: Node): boolean =>
    (ts.isTypeReferenceNode(t) && ts.isIdentifier(t.typeName) && t.typeName.text === name) ||
    (t.forEachChild(names) ?? false);
  if (!node.type || names(node.type)) scope.fail(node, "a mapped type's value names its key");
  const plus = (token: Node | undefined, keyword: ts.SyntaxKind) =>
    !!token && (token.kind === keyword || token.kind === ts.SyntaxKind.PlusToken);
  const key = parameter.constraint && scope.keys?.(parameter.constraint);
  return { key: key ?? typeTerm(scope, parameter.constraint, parameter), value: typeTerm(scope, node.type),
    optional: plus(node.questionToken, ts.SyntaxKind.QuestionToken),
    readonly: plus(node.readonlyToken, ts.SyntaxKind.ReadonlyKeyword) };
}

/** A mapped type at a known key, as TypeScript expands it: over string and
 * number literals, one field per property they name; over `string`, a string
 * index, which `number` and every string literal add nothing to; over
 * `number`, a number index, which number literals add nothing to; over
 * `symbol`, a symbol index. Its value does not name the key, so every field
 * and index has the one value type. A type parameter is refused. */
export function expandMapped(m: Mapped, span: Span, fail: (message: string) => never): TypeTerm {
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
  return { k: "object", fields: names.map(name => ({ name, optional: m.optional, readonly: m.readonly,
    type: m.value, span })), ...indexes, calls: [], span };
}

/** `term` with each of its declaration's parameters replaced by the term at
 * that position of `args`. */
export function substitute(term: TypeTerm, args: readonly TypeTerm[]): TypeTerm {
  const go = (t: TypeTerm): TypeTerm => substitute(t, args);
  const fn = (f: FunctionTerm): FunctionTerm => ({ ...f, receiver: f.receiver && go(f.receiver),
    params: f.params.map(go), rest: f.rest && go(f.rest), result: go(f.result) });
  switch (term.k) {
    case "parameter": {
      const arg = args[term.index];
      if (!arg) throw Error("declaration parameter index outside its application");
      return arg;
    }
    case "atom": case "literal": case "unique": case "self": case "binder": case "callable": return term;
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
      result: go(term.result) };
    case "pack": return { ...term, of: go(term.of) };
    case "scheme": return { ...term, binders: term.binders.map(b => ({ ...b, bound: b.bound && go(b.bound),
      default: b.default && go(b.default) })), signatures: term.signatures.map(f => f.k === "function" ? fn(f)
        : { ...f, params: f.params.map(go), rest: f.rest && go(f.rest), result: go(f.result) }) };
    case "reference": return { ...term, args: term.args.map(go) };
  }
}

/** A tuple element's kind and type, read through its name when it has one. */
function tupleMember(element: TypeNode): { kind: "required" | "optional" | "rest"; type: TypeNode } {
  if (ts.isNamedTupleMember(element))
    return { kind: element.dotDotDotToken ? "rest" : element.questionToken ? "optional" : "required",
      type: element.type };
  if (ts.isRestTypeNode(element)) return { kind: "rest", type: element.type };
  if (ts.isOptionalTypeNode(element)) return { kind: "optional", type: element.type };
  return { kind: "required", type: element };
}

function tuple(scope: TermScope, node: ts.TupleTypeNode, readonly: boolean, span: Span): TypeTerm {
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
function intersection(scope: TermScope, node: ts.IntersectionTypeNode, span: Span): TypeTerm {
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
    declared = false): FunctionTerm {
  const [only, ...more] = signatures(scope, parameters, result, at, span, declared);
  if (!only || more.length) return scope.fail(at, "a rest parameter over several tuples is several signatures");
  return only;
}

/** A generic signature's binders and forms: its own type parameters are
 * binders, named by spelling, which shadow the enclosing ones. */
function quantified(scope: TermScope, typeParameters: readonly ts.TypeParameterDeclaration[],
    parameters: readonly ts.ParameterDeclaration[], result: TypeNode, at: Node, span: Span) {
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
    result: TypeNode | undefined, at: Node, span: Span, declared = false,
    // A result the caller states instead of reading `result`, such as the
    // receiver a library overlay puts for a `this` result.
    given?: TypeTerm): FunctionTerm[] {
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
          if (!contract || !("positions" in contract)) return scope.fail(p, restRefusal(part));
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
      if ("positions" in contract) params.push(...contract.positions);
      else rest = contract.element;
    } else {
      if (!optional(p) && firstOptional >= 0 && index > firstOptional)
        scope.fail(p, "a required parameter cannot follow an optional one");
      const type = typeTerm(scope, p.type, p);
      params.push(optional(p) ? optionalTerm(type, spanOf(scope, p)) : type);
    }
  }
  const resultTerm = given ?? typeTerm(scope, result, at);
  return (alternatives ?? [[]]).map(positions =>
    ({ k: "function", effect: "unrestricted", receiver, params: [...params, ...positions], rest, result: resultTerm, span }));
}

/** Several signatures as one term: their intersection, which a value meets by
 * meeting each. */
export function oneTerm(terms: FunctionTerm[], span: Span): TypeTerm {
  return terms.length === 1 && terms[0] ? terms[0] : { k: "intersection", parts: terms, span };
}

/** A member's key: an identifier, a declaration's string literal, or a
 * computed `[x]` whose `x` the scope resolves to a `unique symbol` constant.
 * Anything else has no key here. */
function propertyKey(scope: TermScope, name: Node | undefined): PropertyKey | null {
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
    methods: boolean | "nested"): TypeTerm {
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
function sameIndex(a: { readonly: boolean; value: TypeTerm }, b: { readonly: boolean; value: TypeTerm }): boolean {
  const spanless = (t: TypeTerm): string => JSON.stringify(t, (key, value: unknown) => key === "span" ? undefined : value);
  return a.readonly === b.readonly && spanless(a.value) === spanless(b.value);
}

/** The key kinds an index signature's parameter type names: `string`,
 * `number`, `symbol`, or a union of them. */
function indexKinds(scope: TermScope, node: TypeNode): ("string" | "number" | "symbol")[] {
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
export function classInstance(scope: TermScope, node: ts.ClassDeclaration, span: Span): TypeTerm {
  const fields: Extract<TypeTerm, { k: "object" }>["fields"] = [];
  const names = new Set<string>();
  const named = (member: ts.ClassElement & { name?: Node }): PropertyKey => {
    const name = member.name;
    // A private name `#x` is a key of its own, a symbol no code outside the
    // class spells (PROGRAM-TYPING.md, "Classes").
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
        const method = signature(inner, member.parameters, member.type, member, memberSpan);
        if (method.receiver) scope.fail(member, GENERIC_METHOD_RECEIVER);
        fields.push({ name, optional: false, readonly: true,
          type: { k: "scheme", binders, signatures: [{ ...method, receiver: { k: "self", span: memberSpan } }],
            span: memberSpan }, span: memberSpan });
        continue;
      }
      const method = signature(scope, member.parameters, member.type, member, memberSpan);
      fields.push({ name, optional: false, readonly: true,
        type: { ...method, receiver: hostReceiver(method, memberSpan) }, span: memberSpan });
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
  return { k: "object", fields, stringIndex: null, calls: [], span };
}
