/** Types TypeScript computes from other types: `typeof x`, `keyof T`, `T[K]`,
 * template literal types, conditional types and applications of aliases computed from their
 * parameters (SOURCE-CONTRACTS.md, "Computed types"). Their meaning is the type
 * TypeScript computes, which the checker gives; this module states it as the
 * equivalent type term the fragment already has, or refuses it with the
 * reason no such term exists. Nothing here is a second reading of type
 * syntax: a type the result names is read by `type-term.mts`, where it is
 * declared. What is read from the checker's types is only what has no
 * syntax: a union of literals and primitives, and the record an object
 * literal's inferred type is. */
import { childOf, childrenOf, isStatic, isTypeAlias } from "./syntax.mts";
import { SignatureKind, SymbolFlags, TypeFlags, isBigIntLiteralType, isBooleanLiteralType, isClassOrInterfaceType, isConditionalType, isIndexType, isIndexedAccessType, isNumberLiteralType, isStringLiteralType, isStringMappingType, isSubstitutionType, isTemplateLiteralType, isTypeParameter, isTypeReference, isUnionType, type Checker, type Type } from "typescript/unstable/sync";
import * as ts from "typescript/unstable/ast";
import type { Node, TypeAliasDeclaration, TypeNode, TypeReferenceNode } from "typescript/unstable/ast";
import type { Span } from "./span.mts";
import type { DeclarationIdentity, TypeTerm } from "./declaration-types.mts";
import { computedAlias, computedForm, isEmptyObject, numericKey, optionalTerm, reduceLiteralIntersection } from "./type-term.mts";
import { passToolFailure } from "./thrown.mts";

/** A reader of type syntax: it may read the checker and grow the stores it
 * reaches, as the type reader does, and changes no other value. */
export type TypeReader = (node: TypeNode) => Modifies<{ values: "any"; spines: "grow" }, TypeTerm>;

/** What the evaluator reads with: the project's checker, and the reader of a
 * declaration's own annotation, in that declaration's scope, with the binders
 * of the functions enclosing it (`binders`), or of the value a name denotes, as
 * an import of it is read. */
export type ComputedContext = {
  checker: Checker;
  annotation(node: TypeNode, at: Node, binders: string[]): TypeTerm;
  /** A type alias's equation read as the declaration's own body, as the
   * declaration graph reads it: a method of its type literal takes the
   * declaration as its receiver (`self`). */
  body(alias: TypeAliasDeclaration): TypeTerm;
  /** An optional method of an interface, read where it is declared: its
   * signatures, each received by the declaration (`self`). */
  method(node: ts.MethodSignatureDeclaration): TypeTerm;
  /** The type of the value `declarations` bind, read as an imported one's
   * is, with its binders (a generic value has some). */
  value(declarations: readonly Node[], what: string): { typeParams: readonly unknown[]; type: TypeTerm };
  /** The type alias a reference names, as TypeScript resolves it, if it
   * names one. */
  alias: (reference: TypeReferenceNode) => TypeAliasDeclaration | null;
  /** The declaration named by the current projected reference. */
  referenceAlias(reference: Extract<TypeTerm, { k: "reference" }>): TypeAliasDeclaration | null;
  /** The reader of type syntax inside `alias`'s declaration with its
   * parameters read as `args`, in the alias's own scope, a computed form
   * naming them evaluated by TypeScript at the application `use`. */
  applied(alias: TypeAliasDeclaration, args: readonly TypeTerm[], use: Node): TypeReader;
  /** A generic alias's equation at a reference's arguments, when it is an
   * array, a tuple or another alias's application; null otherwise. */
  equation(reference: Extract<TypeTerm, { k: "reference" }>): TypeTerm | null;
  /** Throws where `node` names a type declared in a block one of whose
   * captured binders a nearer declaration hides there (SOURCE-CONTRACTS.md,
   * "Block-scoped type declarations"): TypeScript's evaluation would read
   * it past that refusal; and where `node` reads the verifier's `SafeInt`,
   * which TypeScript's evaluation reads as `number`. */
  captures(node: TypeNode): void;
  /** The identity of the symbol a `unique symbol` type names: the index of
   * the `unique symbol` constant or well-known symbol declaring it among the
   * listed symbols, as a computed key `[k]` naming it is read. Throws the
   * reason where the symbol it holds is not known. */
  unique: (type: Type) => number;
  /** Whether a declaration belongs to the standard library (`lib.*.d.ts`). */
  isLibrary?: (node: Node) => boolean;
  /** Declaration metadata for the `Ref` in `T extends Ref<infer ...>`. */
  conditionalTarget?: (ref: TypeReferenceNode) => ConditionalTargetInfo | null;
  /** Structural/inheritance metadata for a `reference` term tested against `Ref<infer ...>`. */
  conditionalMember?: (ref: Extract<TypeTerm, { k: "reference" }>) => MemberReferenceInfo | null;
  /** Evaluate a branch of a conditional type with `infer` type parameters bound. */
  withBindings?: (node: TypeNode, bindings: ReadonlyMap<string, TypeTerm>, baseRead: TypeReader) => TypeTerm;
};

/** Declaration metadata for the target `Ref` of `T extends Ref<infer ...>`. */
export type ConditionalTargetInfo = {
  identity: DeclarationIdentity;
  paramCount: number;
  paramBounds: readonly (TypeTerm | null)[];
  requiredProps: readonly string[];
  hasNominalMember: boolean;
  isClassOrInterface: boolean;
  allParamsUsed: boolean;
  isLibraryWrapper: boolean;
};

/** Metadata for a concrete reference `member` tested against `Ref<infer ...>`. */
export type MemberReferenceInfo = {
  unfolded: TypeTerm | null;
  bases: readonly TypeTerm[];
  props: readonly string[] | null;
  hasStringIndex: boolean;
};

/** Whether a checker type denotes class instances or an interface, including
 * an instantiated generic reference. A class constructor shares the instance
 * symbol but has neither of these object kinds. */
export function isInstanceReference(type: Type): boolean {
  return isTypeReference(type) ? isClassOrInterfaceType(type.getTarget()) : isClassOrInterfaceType(type);
}

/** The number's decimal spelling, as a literal type's text is written. */
function numberText(value: number): string | null {
  return Number.isFinite(value) ? String(value) : null;
}

/** A bigint literal type's value by its decimal spelling. The synchronous
 * API decodes the decimal spelling it is sent as into a `bigint`, and leaves
 * a null or missing one undefined (`sync/api.js`), which the declared
 * `bigint` does not state: any value other than a bigint has no spelling. */
function bigintValue(value: unknown): string | null {
  return typeof value === "bigint" ? String(value) : null;
}

/** `type` as a union of the fragment's primitive families and literals, when
 * it is exactly one: each part a literal (string, number, bigint, Boolean), a
 * primitive family, `null`, `undefined`, `void`, `unknown` or `never`, and,
 * where `unique` identifies symbols, a unique symbol. An enum literal, an
 * object, a type parameter or a string pattern is not one, and the answer is
 * null. */
export function literalUnion(type: Type, span: Span, unique?: (part: Type) => number): TypeTerm | null {
  const parts = isUnionType(type) ? type.getTypes() : [type];
  const terms: TypeTerm[] = [];
  const atom = (name: Extract<TypeTerm, { k: "atom" }>["name"]): TypeTerm => ({ k: "atom", name, span });
  for (const part of parts) {
    const f = part.flags;
    if (f & TypeFlags.EnumLiteral) return null;
    if (isStringLiteralType(part)) terms.push({ k: "literal", name: "string", text: part.value, span });
    else if (isNumberLiteralType(part)) {
      const text = numberText(part.value);
      if (text === null) return null;
      terms.push({ k: "literal", name: "number", text, span });
    } else if (isBigIntLiteralType(part)) {
      const text = bigintValue(part.value);
      if (text === null) return null;
      terms.push({ k: "literal", name: "bigint", text, span });
    } else if (isBooleanLiteralType(part))
      terms.push(part.value
        ? { k: "literal", name: "true", text: "true", span }
        : { k: "literal", name: "false", text: "false", span });
    else if (f & TypeFlags.String) terms.push(atom("string"));
    else if (f & TypeFlags.Number) terms.push(atom("number"));
    else if (f & TypeFlags.BigInt) terms.push(atom("bigint"));
    else if (f & TypeFlags.ESSymbol) terms.push(atom("symbol"));
    else if (f & TypeFlags.UniqueESSymbol && unique) terms.push({ k: "unique", symbol: unique(part), span });
    else if (f & TypeFlags.Null) terms.push(atom("null"));
    else if (f & TypeFlags.Undefined) terms.push(atom("undefined"));
    else if (f & TypeFlags.Void) terms.push(atom("void"));
    else if (f & TypeFlags.Unknown) terms.push(atom("unknown"));
    else if (f & TypeFlags.Never) terms.push(atom("never"));
    else return null;
  }
  const [only] = terms;
  if (!only) return atom("never");
  return terms.length === 1 ? only : { k: "union", parts: terms, span };
}

/** The names of the type parameters of every declaration enclosing `node`:
 * the binders an annotation there reads by spelling. */
export function enclosingBinders(node: Node): string[] {
  const names: string[] = [];
  for (let at: Node | undefined = node.parent; at; at = at.parent) {
    for (const p of childrenOf(at, "typeParameters"))
      if (ts.isTypeParameterDeclaration(p)) names.push(p.name.text);
  }
  return names;
}

const describe = (checker: Checker, type: Type): string => checker.typeToString(type);

/** The type term of a computed type `node` (`computedForm`), located at
 * `span`; `read` reads an operand in the scope `node` is written in. */
export function computedType(context: ComputedContext, node: TypeNode, span: Span,
    read: TypeReader): TypeTerm {
  const { checker } = context;
  const form = computedForm(node) ?? "a computed type";
  context.captures(node);
  // Sound TypeTerm-level conditional evaluation must run BEFORE `literalUnion`
  // so TScert never trusts TS's structural `extends` check for ambiguous cases
  // even when the result happens to be a primitive or literal.
  if (ts.isConditionalTypeNode(node)) {
    const tupleNeverInner = isTupleNeverConditional(node);
    if (tupleNeverInner) {
      return evaluateTupleNeverConditional(node, read(tupleNeverInner), span, read);
    }
    const bareRef = isBareReferenceConditional(node);
    if (isReferenceInferConditional(node) || (bareRef && context.conditionalTarget?.(bareRef))) {
      const checkTerm = read(node.checkType);
      return evaluateConditionalOnTerm({
        body: node,
        checkTerm,
        distributive: false,
        span,
        readBranch: (branch, bindings) =>
          context.withBindings ? context.withBindings(branch, bindings, read) : read(branch),
        targetInfo: ref => context.conditionalTarget?.(ref) ?? null,
        memberInfo: ref => context.conditionalMember?.(ref) ?? null,
      });
    }
  }
  if (ts.isTypeReferenceNode(node)) {
    const alias = context.alias(node);
    if (alias && computedAlias(alias, context.alias, new Set(), context.isLibrary)) {
      let body = alias.type;
      while (ts.isParenthesizedTypeNode(body)) body = body.type;
      const mappedIndexed = ts.isIndexedAccessTypeNode(body) && (() => {
        let obj = body.objectType;
        while (ts.isParenthesizedTypeNode(obj)) obj = obj.type;
        return ts.isMappedTypeNode(obj);
      })();
      const soundConditional = ts.isConditionalTypeNode(body) && (
        isTupleNeverConditional(body) !== null ||
        isReferenceInferConditional(body) ||
        (() => { const b = isBareReferenceConditional(body); return !!b && !!context.conditionalTarget?.(b); })()
      );
      if (soundConditional || ts.isMappedTypeNode(body) || ts.isIntersectionTypeNode(body) || mappedIndexed) {
        const type = checker.getTypeFromTypeNode(node);
        const computed = type && !type.isErrorType() ? describe(checker, type) : alias.name.text;
        return aliasApplication(context, node, span, read, computed);
      }
    }
  }
  const type = checker.getTypeFromTypeNode(node);
  if (!type || type.isErrorType()) throw Error(`TypeScript computes no type for this ${form}: it is not valid TypeScript`);
  const literals = literalUnion(type, span, context.unique);
  if (literals) return literals;
  const computed = describe(checker, type);
  if (ts.isTypeReferenceNode(node)) return aliasApplication(context, node, span, read, computed);
  if (ts.isTypeQueryNode(node)) return typeQuery(context, node, type, span);
  if (ts.isIndexedAccessTypeNode(node)) return indexedAccess(context, node, type, span, read);
  if (ts.isTemplateLiteralTypeNode(node) || isTemplateLiteralType(type) || isStringMappingType(type))
    throw Error(`the template literal type ${computed} is a string pattern: it holds infinitely many ` +
      "strings, not a union of literals, and the fragment has no string-pattern type");
  if (generic(type))
    throw Error(`${form} over a type parameter, ${computed}, is computed only at an instance`);
  throw Error(`${form} is ${computed}, ${inexpressible(checker, type)}`);
}

/** An application of a computed type alias (`computedAlias`),
 * `ElementOf<readonly E[]>`: its equation evaluated with the alias's
 * parameters read as the reference's arguments, which are read where the
 * reference is written. Where TypeScript computes a union of literals and
 * primitives for the reference, that union was taken already. */
function aliasApplication(context: ComputedContext, node: TypeReferenceNode, span: Span,
    read: TypeReader, computed: string): TypeTerm {
  const alias = context.alias(node);
  if (!alias || !computedAlias(alias, context.alias, new Set(), context.isLibrary))
    throw Error(`${computed} is not an application of a type alias TypeScript computes`);
  // An omitted argument is its parameter's default, read at the earlier
  // arguments.
  const applied = parameterMembers(context, alias, node, read, new Map<Node, Member>());
  if (!applied) throw Error(`${computed} omits an argument of ${alias.name.text} that has no default`);
  let body = alias.type;
  while (ts.isParenthesizedTypeNode(body)) body = body.type;
  const atArguments = context.applied(alias, applied.args, node);
  if (ts.isMappedTypeNode(body) || ts.isIntersectionTypeNode(body)) return atArguments(body);
  if (ts.isIndexedAccessTypeNode(body)) {
    let obj = body.objectType;
    while (ts.isParenthesizedTypeNode(obj)) obj = obj.type;
    if (ts.isMappedTypeNode(obj)) return atArguments(body);
  }
  if (ts.isConditionalTypeNode(body)) return distributed(context, node, alias, body, span, computed, applied.members, atArguments);
  // An application of an alias that is no computed alias, one of whose
  // arguments is computed (`Pick<T, Exclude<keyof T, K>>`), is that alias
  // at the arguments, each evaluated at this reference.
  const target = ts.isTypeReferenceNode(body) ? context.alias(body) : null;
  if (ts.isTypeReferenceNode(body) && !(target && computedAlias(target, context.alias, new Set(), context.isLibrary))) return atArguments(body);
  return computedType(context, body, span, atArguments);
}

/** A union member as written: its type node, the reader of the scope it
 * is written in, and the members the parameters it may name stand for. */
type Member = { node: TypeNode; read: TypeReader; params: ReadonlyMap<Node, Member> };

/** The members `alias`'s parameters stand for at `reference`: each written
 * argument where it is written, each omitted one its default, read at the
 * earlier ones; null where one has neither. */
function parameterMembers(context: ComputedContext, alias: TypeAliasDeclaration, reference: TypeReferenceNode,
    read: TypeReader, params: ReadonlyMap<Node, Member>): { args: TypeTerm[]; members: Map<Node, Member> } | null {
  const args: TypeTerm[] = [];
  const members = new Map<Node, Member>();
  for (const [i, parameter] of (alias.typeParameters ?? []).entries()) {
    const written = reference.typeArguments?.[i];
    const member: Member | null = written ? { node: written, read, params }
      : parameter.defaultType ? { node: parameter.defaultType, read: context.applied(alias, [...args], reference), params: new Map(members) }
      : null;
    if (!member) return null;
    args.push(member.read(member.node));
    members.set(parameter, member);
  }
  return { args, members };
}

/** The members of the union `node` is written as, in the order written: a
 * union's members, and those of the equation of an alias each names, read
 * where that alias is declared, with its parameters read as the reference's
 * arguments or their defaults; a parameter standing alone is the members of
 * what it stands for (`params`). Any other type is one member. */
function unionMembers(context: ComputedContext, node: TypeNode, read: TypeReader,
    seen: Set<Node> = new Set<Node>(), params: ReadonlyMap<Node, Member> = new Map<Node, Member>()): Member[] {
  while (ts.isParenthesizedTypeNode(node)) node = node.type;
  if (ts.isUnionTypeNode(node)) return node.types.flatMap(t => unionMembers(context, t, read, seen, params));
  if (ts.isTypeReferenceNode(node) && ts.isIdentifier(node.typeName) && !node.typeArguments?.length) {
    const declarations = (context.checker.getSymbolAtLocation(node.typeName)?.declarations ?? []).map(d => d.resolve());
    const standing = declarations.map(d => d && params.get(d)).find(m => m !== undefined);
    if (standing) return unionMembers(context, standing.node, standing.read, seen, standing.params);
  }
  const alias = ts.isTypeReferenceNode(node) ? context.alias(node) : null;
  // A computed alias has no equation to read members from.
  const computed = (n: Node): boolean => computedAlias(n, context.alias, new Set(), context.isLibrary);
  if (!alias || !ts.isTypeReferenceNode(node) || seen.has(alias) || enclosingBinders(alias).length || computed(alias))
    return [{ node, read, params }];
  const applied = parameterMembers(context, alias, node, read, params);
  if (!applied) return [{ node, read, params }];
  return unionMembers(context, alias.type, context.applied(alias, applied.args, node), new Set<Node>([...seen, alias]), applied.members);
}

/** An application of an alias whose equation is a conditional type
 * distributing over its parameter, `Extract<T, U>`, which is
 * `T extends U ? T : never`: where TypeScript decides it for each member of
 * the argument's union, and its result is a union of whole members, it is
 * the union of those members, each read as written. Where TypeScript computes
 * a union of literals and primitives for it, that union was taken already. */
function distributed(context: ComputedContext, node: TypeReferenceNode, alias: TypeAliasDeclaration,
    body: ts.ConditionalTypeNode, span: Span, computed: string, args: ReadonlyMap<Node, Member>,
    atArguments: TypeReader): TypeTerm {
  const { checker } = context;
  let check = body.checkType;
  while (ts.isParenthesizedTypeNode(check)) check = check.type;
  const index = ts.isTypeReferenceNode(check) && ts.isIdentifier(check.typeName) && !check.typeArguments?.length
    ? (alias.typeParameters ?? []).findIndex(p => ts.isIdentifier(check.typeName) && p.name.text === check.typeName.text)
    : -1;
  const parameter = (alias.typeParameters ?? [])[index];
  const decided = parameter && args.get(parameter);
  const tupleNeverInner = isTupleNeverConditional(body);
  if (tupleNeverInner) {
    return evaluateTupleNeverConditional(body, atArguments(tupleNeverInner), span, atArguments);
  }
  const bareRef = isBareReferenceConditional(body);
  if (isReferenceInferConditional(body) || (bareRef && context.conditionalTarget?.(bareRef))) {
    const checkTerm = decided
      ? (() => {
          const ms = unionMembers(context, decided.node, decided.read, new Set<Node>(), decided.params).map(m => m.read(m.node));
          const [only] = ms;
          return !only ? { k: "atom" as const, name: "never" as const, span } : ms.length === 1 ? only : { k: "union" as const, parts: ms, span };
        })()
      : atArguments(body.checkType);
    return evaluateConditionalOnTerm({
      body,
      checkTerm,
      distributive: !!decided,
      span,
      readBranch: (branch, bindings) =>
        context.withBindings ? context.withBindings(branch, bindings, atArguments) : atArguments(branch),
      targetInfo: ref => context.conditionalTarget?.(ref) ?? null,
      memberInfo: ref => context.conditionalMember?.(ref) ?? null,
    });
  }
  const type = checker.getTypeFromTypeNode(node);
  if (!type || generic(type))
    throw Error(`a conditional type over a type parameter, ${computed}, is computed only at an instance`);
  if (!decided)
    throw Error(`the conditional type ${alias.name.text} decides a type other than one of its parameters, ` +
      `${computed}: it distributes over no union`);
  const argument = decided.node;
  const members = unionMembers(context, argument, decided.read, new Set<Node>(), decided.params);
  const inferred = inferredResult(context, alias, body, members, span);
  if (inferred) return inferred;
  const results = isUnionType(type) ? type.getTypes() : [type];
  const ids = new Set(results.map(t => t.id));
  const covered = new Set<number>();
  const kept = members.filter(member => {
    const memberType = checker.getTypeFromTypeNode(member.node);
    if (!memberType) return false;
    const parts = isUnionType(memberType) ? memberType.getTypes() : [memberType];
    if (!parts.every(p => ids.has(p.id))) return false;
    parts.forEach(p => covered.add(p.id));
    return true;
  });
  const other = results.find(t => !covered.has(t.id));
  if (other)
    throw Error(`${alias.name.text} at its arguments is ${computed}, whose part ${describe(checker, other)} is ` +
      `no member of ${argument.getText(argument.getSourceFile())} as written: it is no selection of that union's ` +
      "members (a member naming a type parameter is another type at each instance)");
  const terms = kept.map(member => member.read(member.node));
  const [only] = terms;
  if (!only) return { k: "atom", name: "never", span };
  return terms.length === 1 ? only : { k: "union", parts: terms, span };
}

/** An application of an alias whose equation infers from a function or
 * constructor type: `ReturnType<T>`,
 * `T extends (...args: any) => infer R ? R : any`, its result;
 * `Parameters<T>`, `T extends (...args: infer P) => any ? P : never`, and
 * `ConstructorParameters<T>`, of `abstract new (...args: infer P) => any`,
 * its parameter list. The extends type matches every function (every
 * class), so at a member that is one the answer is its declared result or
 * parameter list, of its last signature where it has several, as
 * TypeScript infers from an overload set; at a union, the union of its
 * members' answers. Null where the equation is of another form; refused
 * where a member is no function (class) the reader states the signatures
 * of. */
function inferredResult(context: ComputedContext, alias: TypeAliasDeclaration, body: ts.ConditionalTypeNode,
    members: readonly Member[], span: Span): TypeTerm | null {
  let written = body.extendsType;
  while (ts.isParenthesizedTypeNode(written)) written = written.type;
  const construct = ts.isConstructorTypeNode(written);
  if (!ts.isFunctionTypeNode(written) && !ts.isConstructorTypeNode(written)) return null;
  const extendsType: ts.FunctionTypeNode | ts.ConstructorTypeNode = written;
  if (!extendsType.type) return null;
  const [rest, ...others] = extendsType.parameters;
  const result = extendsType.type;
  const restType = rest?.type;
  const inferred = ts.isInferTypeNode(result) ? { at: "result" as const, infer: result.typeParameter }
    : restType && ts.isInferTypeNode(restType) ? { at: "parameters" as const, infer: restType.typeParameter } : null;
  if (!inferred) return null;
  const trueType = body.trueType;
  const any = (n: Node | undefined): boolean => n?.kind === ts.SyntaxKind.AnyKeyword;
  if (extendsType.typeParameters?.length || inferred.infer.constraint || others.length || !rest?.dotDotDotToken ||
      (construct && inferred.at === "result") ||
      // Every class value meets `abstract new (...)`; a concrete `new (...)`
      // excludes an abstract class, whose typeof then takes the false arm.
      (construct && !extendsType.modifiers?.some(m => m.kind === ts.SyntaxKind.AbstractKeyword)) ||
      (!construct && !!extendsType.modifiers?.length) ||
      !any(inferred.at === "result" ? restType : result) || !ts.isTypeReferenceNode(trueType) ||
      !ts.isIdentifier(trueType.typeName) || trueType.typeName.text !== inferred.infer.name.text || trueType.typeArguments?.length)
    throw Error(`the conditional type ${alias.name.text} infers from a function type other than ` +
      "`(...args: any) => infer R` with result `R`, or `(...args: infer P) => any` or " +
      "`abstract new (...args: infer P) => any` with result `P`");
  const answers = members.map(member => {
    const written = member.node.getText(member.node.getSourceFile());
    const refused = (): never => {
      throw Error(`${alias.name.text} of ${written}: ${written} is no ${construct ? "class" : "function"} ` +
        "whose signatures the reader states");
    };
    const query = member.node;
    const declarations = ts.isTypeQueryNode(query)
      ? (context.checker.getSymbolAtLocation(ts.isIdentifier(query.exprName) ? query.exprName : query.exprName.right)
        ?.declarations ?? []).map(d => d.resolve()) : [];
    // The declared signatures, overloads where some have no body: TypeScript
    // infers from the last.
    const declared: readonly (ts.FunctionDeclaration | ts.ConstructorDeclaration)[] = construct
      ? declarations.flatMap(d => d && ts.isClassDeclaration(d)
        ? d.members.filter((m): m is ts.ConstructorDeclaration => ts.isConstructorDeclaration(m)) : [])
      : declarations.filter((d): d is ts.FunctionDeclaration => !!d && ts.isFunctionDeclaration(d));
    if (declared.some(f => f.type && ts.isTypePredicateNode(f.type)))
      throw Error(`${alias.name.text} of ${written}: a guard's result is its Boolean, which its signatures state beside its promise`);
    const signatures: readonly (ts.FunctionDeclaration | ts.ConstructorDeclaration | ts.FunctionTypeNode)[] =
      !construct && ts.isFunctionTypeNode(query) ? [query]
        : declared.some(f => !f.body) ? declared.filter(f => !f.body) : declared;
    const term = member.read(member.node);
    const kind = construct ? "constructor" : "function";
    const forms = term.k === kind ? [term]
      : term.k === "intersection" && term.parts.every(p => p.k === kind) ? term.parts : null;
    const last = forms?.[forms.length - 1];
    if (!forms || !last || (last.k !== "function" && last.k !== "constructor")) return refused();
    if (inferred.at === "result") {
      if (declared.length && forms.length !== signatures.length) return refused();
      return last.result;
    }
    // The parameter list as a tuple: each required parameter a required
    // position, each optional one (written `?` or with a default) an optional
    // position at its type, which holds the `undefined` an omitted argument
    // gives, and a rest its rest.
    const signature = signatures[signatures.length - 1];
    if (construct && !signature) {
      // A class declaring no constructor: its parameters are its base's.
      const owner = declarations.find(d => !!d && ts.isClassDeclaration(d));
      if (!owner || !ts.isClassDeclaration(owner) || owner.heritageClauses?.length || last.params.length || last.rest)
        return refused();
      const empty: TypeTerm = { k: "tuple", presence: "dense", readonly: false, required: [], optional: [], rest: null, span };
      return empty;
    }
    if (!signature || forms.length !== signatures.length) return refused();
    const ordinary = signature.parameters.filter(p => !(ts.isIdentifier(p.name) && p.name.text === "this"));
    const fixed = ordinary.filter(p => !p.dotDotDotToken);
    const optionalFrom = fixed.findIndex(p => !!p.questionToken || !!p.initializer);
    if (fixed.length !== last.params.length || (last.rest && last.rest.k === "pack") ||
        (optionalFrom >= 0 && fixed.slice(optionalFrom).some(p => !p.questionToken && !p.initializer)))
      return refused();
    const cut = optionalFrom < 0 ? fixed.length : optionalFrom;
    const list: TypeTerm = { k: "tuple", presence: "dense", readonly: false, required: last.params.slice(0, cut),
      optional: last.params.slice(cut), rest: last.rest, span };
    return list;
  });
  const [only] = answers;
  if (!only) return { k: "atom", name: "never", span };
  return answers.length === 1 ? only : { k: "union", parts: answers, span };
}

/** The first member outside the union of literals and primitives, or `type`
 * when every member is expressible. */
function inexpressiblePart(type: Type): Type {
  const parts = isUnionType(type) ? type.getTypes() : [type];
  for (const part of parts) {
    if (literalUnion(part, [0, 0]) === null) return part;
  }
  return type;
}

/** Why `type` is not a union of literals and primitives: its first part that
 * is not one. */
function inexpressible(checker: Checker, type: Type): string {
  const part = inexpressiblePart(type);
  const what = part.flags & TypeFlags.EnumLiteral ? "an enum member, outside the fragment"
    : "not a literal or a primitive";
  return `whose part ${checker.typeToString(part)} is ${what}`;
}

/** Whether `type` still names a type parameter: TypeScript defers it. */
function generic(type: Type): boolean {
  if (isTypeParameter(type) || isIndexType(type) || isIndexedAccessType(type) || isConditionalType(type) ||
      isSubstitutionType(type)) return true;
  return isUnionType(type) && type.getTypes().some(generic);
}

/** The declaration of the value or member a name denotes, with the type node
 * it is annotated with, if it has one. */
type Declared = { node: Node; annotation: TypeNode | undefined; optional: boolean };

function declared(node: Node): Declared {
  const annotation = ts.isVariableDeclaration(node) || ts.isParameterDeclaration(node) ||
    ts.isPropertySignatureDeclaration(node) || ts.isPropertyDeclaration(node) ? node.type : undefined;
  const optional = !!childOf(node, "questionToken") ||
    childOf(node, "postfixToken")?.kind === ts.SyntaxKind.QuestionToken;
  return { node, annotation, optional };
}

/** `typeof x` and `typeof x.y`: the value's type as its declaration states
 * it. A function or class is read as an imported one is; a binding or member
 * by its annotation, which must denote exactly the type TypeScript computes
 * for the query (not a narrowed one, nor an instance of a generic member). A
 * binding TypeScript types by inference has no annotation to read. */
function typeQuery(context: ComputedContext, node: ts.TypeQueryNode, type: Type, span: Span): TypeTerm {
  const { checker } = context;
  const computed = describe(checker, type);
  if (node.typeArguments?.length) throw Error("typeof with type arguments is an instantiation, outside the fragment");
  const name = node.exprName;
  const last = ts.isIdentifier(name) ? name : name.right;
  const what = `typeof ${name.getText(node.getSourceFile())}`;
  const symbol = checker.getSymbolAtLocation(last);
  // A name that is also an interface or type alias denotes its value here.
  const nodes = (symbol?.declarations ?? []).map(d => d.resolve()).filter((d): d is Node =>
    !!d && !ts.isInterfaceDeclaration(d) && !isTypeAlias(d));
  const [first] = nodes;
  if (!first) throw Error(`${what} names nothing TypeScript declares`);
  // An annotation's `typeof E` is the enum's object type, which the parser
  // reads (SOURCE-CONTRACTS.md, "Enums"); the declaration reader does not read enums.
  if (ts.isEnumDeclaration(first))
    throw Error(`${what} is an enum's object type, which only an annotation of the enum's module states`);
  if (nodes.every(n => ts.isFunctionDeclaration(n)) || (nodes.length === 1 && ts.isClassDeclaration(first))) {
    const value = context.value(nodes, what);
    if (value.typeParams.length) throw Error(`${what} is generic, ${computed}: a generic value type is outside the fragment`);
    // A class value reaches the static members of its base classes through
    // its prototype chain, which TypeScript's `typeof C` states and the class
    // value's type does not: such an annotation is refused, not cut short.
    if (ts.isClassDeclaration(first) && symbol) {
      const classType = checker.getTypeOfSymbol(symbol);
      const inherited = (classType ? checker.getPropertiesOfType(classType) : [])
        .filter(p => p.name !== "prototype" && !p.declarations.some(d => d.resolve()?.parent === first))
        .map(p => p.name);
      if (inherited.length)
        throw Error(`${what} is a class inheriting static members of its base (${inherited.join(", ")}): its ` +
          "class value reaches them through its prototype, which no member of the class value's type states");
    }
    if (!ts.isClassDeclaration(first) || !first.members.some(member => isStatic(member))) return value.type;
    // A class value's static fields are own data properties of it, which its
    // type states; its static methods are bindings of their own, which no
    // member of its type states.
    const statics = first.members.filter(member => isStatic(member)).flatMap(member => {
      if (ts.isClassStaticBlockDeclaration(member)) return [];
      if (!ts.isPropertyDeclaration(member) || !ts.isIdentifier(member.name))
        throw Error(`${what} is a class with static methods or private statics: they are bindings of their own, ` +
          "not members of the class value's type");
      const field = member.name.text;
      const symbol = checker.getSymbolAtLocation(member.name);
      const inferred = symbol ? checker.getTypeOfSymbol(symbol) : undefined;
      const fieldType = member.type ? context.annotation(member.type, member, enclosingBinders(member))
        : inferred ? literalUnion(inferred, span) : null;
      if (!fieldType) throw Error(`${what}: the static field '${field}' has neither an annotation nor a literal type`);
      return [{ name: field, type: fieldType }];
    });
    if (value.type.k !== "constructor") throw Error(`${what} is a class read as other than its construct signature`);
    return statics.length ? { ...value.type, statics } : value.type;
  }
  if (nodes.length !== 1) throw Error(`${what} has ${nodes.length} declarations`);
  const { annotation, optional } = declared(first);
  if (!annotation) {
    // A constant's inferred type is that of its initializer, which a later
    // assignment cannot change: an object literal's is a record read as the
    // checker states it.
    const inferred = ts.isVariableDeclaration(first) && isConstant(first) ? inferredTerm(checker, type, span) : null;
    if (inferred) return inferred;
    throw Error(`${what} is ${computed}, the type TypeScript infers for a binding without an ` +
      "annotation, and not a union of literals and primitives or an object literal's record of them");
  }
  const stated = checker.getTypeFromTypeNode(annotation);
  const same = stated?.id === type.id;
  // `x?: T` is `T | undefined` where it is read.
  const orUndefined = optional && !same && stated !== undefined &&
    checker.getNonNullableType(type)?.id === checker.getNonNullableType(stated)?.id &&
    isUnionType(type) && type.getTypes().some(t => (t.flags & TypeFlags.Undefined) !== 0);
  if (!same && !orUndefined)
    throw Error(`${what} is ${computed}, not the type its declaration states (a narrowed binding, or a ` +
      "member of a generic type's instance)");
  const term = context.annotation(annotation, first, enclosingBinders(first));
  return orUndefined ? optionalTerm(term, span) : term;
}

/** Whether a variable is declared `const`. */
function isConstant(node: ts.VariableDeclaration): boolean {
  const list = node.parent;
  return !!list && ts.isVariableDeclarationList(list) && (list.flags & ts.NodeFlags.Const) !== 0;
}

/** Whether `node` is inside a `const` assertion, `e as const`, which makes
 * an object literal's properties readonly. */
function underConstAssertion(node: Node): boolean {
  for (let at: Node | undefined = node.parent; at; at = at.parent) {
    if (ts.isAssertionExpression(at) && ts.isTypeReferenceNode(at.type) &&
        ts.isIdentifier(at.type.typeName) && at.type.typeName.text === "const") return true;
    if (ts.isVariableDeclaration(at)) return false;
  }
  return false;
}

/** The type TypeScript infers for an object literal, as the term that states
 * it: its properties, each a writable field (an object literal's property is
 * one) of a union of literals and primitives or of such a record in turn, and
 * the index signatures a spread copied into it. With `arrays`, where every
 * array type within comes from an array literal, also the array TypeScript
 * infers for one, `T[]` as its annotation reads. Null for anything else: a
 * method, a symbol-keyed or `const`-asserted property, a property a spread
 * copied from a declared type, a tuple, a function. */
export function inferredTerm(checker: Checker, type: Type, span: Span, depth: number = 0,
    arrays: boolean = false): TypeTerm | null {
  const literals = literalUnion(type, span);
  if (literals) return literals;
  if (depth > 8) return null;
  // An array literal's type is `Array<T>`, `T` the union of its elements'
  // widened types; one `as const` is a readonly tuple, not read here.
  if (arrays && checker.isArrayType(type) && isTypeReference(type) && type.getSymbol()?.name === "Array") {
    const [element, ...more] = checker.getTypeArguments(type);
    const term = element && !more.length ? inferredTerm(checker, element, span, depth + 1, arrays) : null;
    return term ? { k: "array", presence: "readable", readonly: false, element: term, span } : null;
  }
  if (!(type.flags & TypeFlags.Object) ||
      checker.getSignaturesOfType(type, SignatureKind.Call).length ||
      checker.getSignaturesOfType(type, SignatureKind.Construct).length) return null;
  const fields: Extract<TypeTerm, { k: "object" }>["fields"] = [];
  for (const property of checker.getPropertiesOfType(type)) {
    const declaration = property.valueDeclaration?.resolve();
    if (!declaration || !(ts.isPropertyAssignment(declaration) || ts.isShorthandPropertyAssignment(declaration)) ||
        !ts.isIdentifier(declaration.name) || declaration.name.text !== property.name ||
        (property.flags & SymbolFlags.Optional) !== 0 || underConstAssertion(declaration)) return null;
    const value = checker.getTypeOfSymbol(property);
    const term = value ? inferredTerm(checker, value, span, depth + 1, arrays) : null;
    if (!term) return null;
    fields.push({ name: property.name, optional: false, readonly: false, type: term, span });
  }
  let stringIndex: { readonly: boolean; value: TypeTerm; span: Span } | null = null;
  let numberIndex: { readonly: boolean; value: TypeTerm; span: Span } | null = null;
  let symbolIndex: { readonly: boolean; value: TypeTerm; span: Span } | null = null;
  for (const info of checker.getIndexInfosOfType(type)) {
    const value = inferredTerm(checker, info.valueType, span, depth + 1, arrays);
    if (!value) return null;
    const index = { readonly: info.isReadonly, value, span };
    const key = info.keyType.flags;
    if (key & TypeFlags.String && !stringIndex) stringIndex = index;
    else if (key & TypeFlags.Number && !numberIndex) numberIndex = index;
    else if (key & TypeFlags.ESSymbol && !symbolIndex) symbolIndex = index;
    else return null;
  }
  return { k: "object", fields, stringIndex, ...(numberIndex ? { numberIndex } : {}),
    ...(symbolIndex ? { symbolIndex } : {}), calls: [], span };
}

/** `T[K]`: the member, element or position of `T` at each key `K` denotes,
 * read from `T` as this scope reads it; a member of a named type is its
 * declaration's annotation, which must denote exactly the type TypeScript
 * computes. */
/** A declaration's equation with its own receiver named: each optional
 * method of its record, an optional field whose function takes the
 * declaration as receiver (`self`), received by `receiver`, the
 * declaration's reference. Every other member keeps its reading, a required
 * method's host-relative receiver included. */
function received(equation: TypeTerm, receiver: Extract<TypeTerm, { k: "reference" }>): TypeTerm {
  if (equation.k !== "object") return equation;
  return { ...equation, fields: equation.fields.map(f => f.optional ? { ...f, type: receivedBy(f.type, receiver) } : f) };
}

/** A method's forms, each received by `self`, received by `receiver`
 * instead; any other type as it is. */
function receivedBy(type: TypeTerm, receiver: TypeTerm): TypeTerm {
  if (type.k === "function" && type.receiver?.k === "self") return { ...type, receiver };
  if (type.k === "intersection" && type.parts.every(p => p.k === "function" && p.receiver?.k === "self"))
    return { ...type, parts: type.parts.map(p => receivedBy(p, receiver)) };
  return type;
}

function indexedAccess(context: ComputedContext, node: ts.IndexedAccessTypeNode, type: Type, span: Span,
    read: TypeReader): TypeTerm {
  const { checker } = context;
  const computed = describe(checker, type);
  const keyType = checker.getTypeFromTypeNode(node.indexType);
  // A key over an alias's parameter is the literals its argument reads as.
  const literal = (t: TypeTerm): boolean =>
    t.k === "literal" || (t.k === "atom" && ["string", "number", "symbol"].includes(t.name)) ||
    (t.k === "union" && t.parts.every(literal));
  const keyTerm = (): TypeTerm | null => {
    const written = read(node.indexType);
    return literal(written) ? written : null;
  };
  const keys = (keyType ? literalUnion(keyType, span) : null) ?? keyTerm();
  if (!keys) throw Error(`the indexed access ${computed} has a key that is not a union of literals and primitives`);
  const keyList = keys.k === "union" ? keys.parts : [keys];
  const union = (parts: TypeTerm[]): TypeTerm => {
    const [only] = parts;
    return parts.length === 1 && only ? only : { k: "union", parts, span };
  };
  const projecting = new Set<TypeAliasDeclaration>();
  const project = (object: TypeTerm, depth: number = 0): TypeTerm => {
    if (depth >= 64)
      throw Error(`the indexed access ${computed} exceeds the projection chain limit of 64`);
    switch (object.k) {
      // Each part projected into a fresh dense array: a `map` with this
      // unrestricted callback may leave a hole, which `TypeTerm[]` excludes.
      case "union": {
        const projected: TypeTerm[] = [];
        for (const part of object.parts) projected.push(project(part, depth + 1));
        return union(projected);
      }
      // An intersection's member at a key is the meet of its operands'
      // members there: `(A[] & B[])[number]` is `A & B`.
      case "intersection": {
        const projected: TypeTerm[] = [];
        for (const part of object.parts) projected.push(project(part, depth + 1));
        return { k: "intersection", parts: projected, span };
      }
      case "array":
        if (keyList.every(k => k.k === "atom" && k.name === "number")) return object.element;
        break;
      case "tuple": {
        const at = (key: TypeTerm): TypeTerm[] => {
          if (key.k === "atom" && key.name === "number")
            return [...object.required, ...object.optional.map(t => optionalTerm(t, span)),
              ...(object.rest ? [object.rest] : [])];
          if (key.k !== "literal" || key.name !== "number" || !/^[0-9]+$/.test(key.text)) return [];
          const i = Number(key.text);
          const position = object.required[i] ?? object.optional[i - object.required.length];
          if (position) return [i < object.required.length ? position : optionalTerm(position, span)];
          return object.rest ? [object.rest] : [];
        };
        const perKey = keyList.map(at);
        if (perKey.every(p => p.length)) return union(perKey.flat());
        break;
      }
      case "object": {
        const parts = keyList.map(key => {
          if (key.k !== "literal" || key.name !== "string") return null;
          const field = object.fields.find(f => f.name === key.text);
          return field ? (field.optional ? optionalTerm(field.type, span) : field.type) : null;
        });
        const found = parts.filter((p: TypeTerm | null): p is TypeTerm => p !== null);
        if (found.length === parts.length) return union(found);
        break;
      }
      case "parameter": case "binder":
        throw Error(`the indexed access ${computed} over a type parameter is computed only at an instance`);
      case "reference": {
        // A type alias without parameters is its equation, read where it is
        // declared.
        const alias = context.referenceAlias(object);
        if (alias && !alias.typeParameters?.length && object.args.length === 0) {
          if (projecting.has(alias))
            throw Error(`the indexed access ${computed} has a cyclic alias projection through ${alias.name.text}`);
          projecting.add(alias);
          try {
            return project(received(context.body(alias), object), depth + 1);
          } finally {
            projecting.delete(alias);
          }
        }
        // A generic alias of an array, a tuple or another alias: its
        // equation at the reference's arguments.
        const equation = object.args.length ? context.equation(object) : null;
        if (equation) return project(equation, depth + 1);
        return member(object);
      }
    }
    throw Error(`the indexed access ${computed} has no member, element or position at its key`);
  };
  // A member of a named type: its declaration's annotation, when that is
  // exactly what TypeScript computes and names no type parameter.
  const member = (reference: Extract<TypeTerm, { k: "reference" }>): TypeTerm => {
    const objectType = checker.getTypeFromTypeNode(node.objectType);
    const [key] = keyList;
    if (!objectType || keyList.length !== 1 || key?.k !== "literal" || key.name !== "string")
      throw Error(`the indexed access ${computed} into a named type needs one string key`);
    const property = checker.getPropertyOfType(objectType, key.text);
    const nodes = (property?.declarations ?? []).map(d => d.resolve()).filter((d): d is Node => !!d);
    const [only] = nodes;
    // An optional method of an interface without parameters is an optional
    // field whose function takes the interface as its receiver: the member is
    // that function or undefined, the type TypeScript computes for it. One
    // the interface inherits takes the interface declaring it as receiver,
    // which the reference does not name.
    if (only && nodes.length === 1 && ts.isMethodSignatureDeclaration(only) &&
        only.postfixToken?.kind === ts.SyntaxKind.QuestionToken && !only.typeParameters?.length &&
        ts.isInterfaceDeclaration(only.parent) && !enclosingBinders(only).length) {
      const owner = only.parent;
      const parts = (objectType.getSymbol()?.declarations ?? []).map(d => d.resolve());
      if (!parts.includes(owner))
        throw Error(`the indexed access ${computed} is an optional method ${owner.name.text} declares, received by ${owner.name.text}, not by the type it is read from`);
      return optionalTerm(receivedBy(context.method(only), reference), span);
    }
    const { annotation, optional } = only && nodes.length === 1 ? declared(only) : { annotation: undefined, optional: false };
    if (!only || !annotation || optional || enclosingBinders(only).length ||
        checker.getTypeFromTypeNode(annotation)?.id !== type.id)
      throw Error(`the indexed access ${computed} is not a member a declaration states as it is`);
    return context.annotation(annotation, only, []);
  };
  try {
    return project(read(node.objectType));
  } catch (error) {
    // TypeScript defers an access it cannot compute before an instance; a
    // tool failure is no refusal.
    passToolFailure(error);
    if (generic(type))
      throw Error(`the indexed access ${computed} over a type parameter is computed only at an instance`);
    throw error;
  }
}


const FUNCTION_PROPS = new Set(["apply", "call", "bind", "prototype", "length", "arguments", "caller", "name", "toString"]);
const ARRAY_PROPS = new Set(["length", "toString", "toLocaleString", "pop", "push", "concat", "join", "reverse",
  "shift", "slice", "sort", "splice", "unshift", "indexOf", "lastIndexOf", "every", "some", "forEach", "map",
  "filter", "reduce", "reduceRight", "find", "findIndex", "fill", "copyWithin", "entries", "keys", "values",
  "includes", "flatMap", "flat", "at"]);

function sameIdentity(a: DeclarationIdentity, b: DeclarationIdentity): boolean {
  return a.module === b.module && a.name === b.name && a.span[0] === b.span[0] && a.span[1] === b.span[1];
}

function flattenUnion(term: TypeTerm): TypeTerm[] {
  return term.k === "union" ? term.parts.flatMap(flattenUnion) : [term];
}

function sameTermList(a: readonly TypeTerm[], b: readonly TypeTerm[]): boolean {
  return a.length === b.length && JSON.stringify(a) === JSON.stringify(b);
}

/** Whether `node` is a non-distributive tuple-wrapped `never` guard
 * `[X] extends [never] ? T : F`. Returns `X` when matched, null otherwise. */
export function isTupleNeverConditional(node: ts.ConditionalTypeNode): TypeNode | null {
  let check = node.checkType;
  while (ts.isParenthesizedTypeNode(check)) check = check.type;
  let ext = node.extendsType;
  while (ts.isParenthesizedTypeNode(ext)) ext = ext.type;
  if (!ts.isTupleTypeNode(check) || check.elements.length !== 1) return null;
  if (!ts.isTupleTypeNode(ext) || ext.elements.length !== 1) return null;
  const checkEl = check.elements[0];
  const extEl = ext.elements[0];
  if (!checkEl || !extEl || ts.isOptionalTypeNode(checkEl) || ts.isRestTypeNode(checkEl) ||
      ts.isNamedTupleMember(checkEl) || ts.isOptionalTypeNode(extEl) || ts.isRestTypeNode(extEl) ||
      ts.isNamedTupleMember(extEl)) return null;
  let innerExt: TypeNode = extEl;
  while (ts.isParenthesizedTypeNode(innerExt)) innerExt = innerExt.type;
  if (innerExt.kind !== ts.SyntaxKind.NeverKeyword) return null;
  return checkEl;
}

/** Whether `node` is a conditional type `Check extends Ref ? T : F` where `Ref`
 * is a 0-arity type reference (no type arguments). Caller checks whether `Ref`
 * resolves to a declared type (not a type parameter). */
export function isBareReferenceConditional(node: ts.ConditionalTypeNode): TypeReferenceNode | null {
  let ext = node.extendsType;
  while (ts.isParenthesizedTypeNode(ext)) ext = ext.type;
  if (!ts.isTypeReferenceNode(ext) || ext.typeArguments?.length) return null;
  return ext;
}

/** Evaluate `[X] extends [never] ? T : F` on a settled `TypeTerm` for `X`. */
export function evaluateTupleNeverConditional(
  body: ts.ConditionalTypeNode,
  checkInnerTerm: TypeTerm,
  span: Span,
  readBranch: (branch: TypeNode) => TypeTerm,
): TypeTerm {
  const parts = flattenUnion(checkInnerTerm);
  for (const part of parts) {
    if (part.k === "binder" || part.k === "parameter")
      throw Error("conditional `[X] extends [never]` on an open type parameter is evaluated only at a concrete instance");
    if (part.k === "reference" && part.reference.target.module === "#deferred-mapped-identity")
      throw Error("conditional `[X] extends [never]` on an unsettled deferred mapped type is outside the fragment");
  }
  const isNever = parts.every(p => p.k === "atom" && p.name === "never");
  void span;
  return readBranch(isNever ? body.trueType : body.falseType);
}

const COND_PRIMITIVE_ATOMS = new Set(["string", "number", "bigint", "boolean", "symbol", "null", "undefined", "void", "never", "unknown"]);

function isCondLiteralOrPrimitive(term: TypeTerm): boolean {
  if (term.k === "literal" || term.k === "unique") return true;
  if (term.k === "atom") return COND_PRIMITIVE_ATOMS.has(term.name);
  if (term.k === "union") return term.parts.every(isCondLiteralOrPrimitive);
  return false;
}

function atomOrLiteralSubtype(part: TypeTerm, extParts: readonly TypeTerm[]): boolean {
  if (part.k === "atom" && part.name === "never") return true;
  if (extParts.some(e => e.k === "atom" && e.name === "unknown")) return true;
  if (part.k === "atom" && part.name === "boolean") {
    if (extParts.some(e => e.k === "atom" && e.name === "boolean")) return true;
    const hasTrue = extParts.some(e => e.k === "literal" && e.name === "true");
    const hasFalse = extParts.some(e => e.k === "literal" && e.name === "false");
    return hasTrue && hasFalse;
  }
  for (const e of extParts) {
    if (part.k === "atom" && e.k === "atom" && part.name === e.name) return true;
    if (part.k === "literal" && e.k === "literal" && part.name === e.name && part.text === e.text) return true;
    if (part.k === "unique" && e.k === "unique" && part.symbol === e.symbol) return true;
    if (part.k === "literal" && e.k === "atom") {
      if (part.name === "string" && e.name === "string") return true;
      if (part.name === "number" && e.name === "number") return true;
      if (part.name === "bigint" && e.name === "bigint") return true;
      if ((part.name === "true" || part.name === "false") && e.name === "boolean") return true;
    }
    if (part.k === "unique" && e.k === "atom" && e.name === "symbol") return true;
  }
  return false;
}

/** Sound exact evaluation of a conditional type whose check and extends operands
 * are settled unions of literals, primitives, and unique symbols (e.g.
 * `Exclude<U, V>` = `T extends U ? never : T`). Returns null if either operand
 * is outside that domain. */
export function evaluateLiteralConditional(
  body: ts.ConditionalTypeNode,
  checkTerm: TypeTerm,
  extTerm: TypeTerm,
  distributive: boolean,
  checkParamName: string | null,
  span: Span,
  readBranch: (branch: TypeNode, bindings: ReadonlyMap<string, TypeTerm>) => TypeTerm,
): TypeTerm | null {
  if (!isCondLiteralOrPrimitive(checkTerm) || !isCondLiteralOrPrimitive(extTerm)) return null;
  const extParts = flattenUnion(extTerm).filter(p => !(p.k === "atom" && p.name === "never"));
  const checkParts = flattenUnion(checkTerm).filter(p => !(p.k === "atom" && p.name === "never"));
  if (distributive) {
    if (!checkParts.length) return { k: "atom", name: "never", span };
    const results: TypeTerm[] = [];
    for (const part of checkParts) {
      const bindings = checkParamName ? new Map<string, TypeTerm>([[checkParamName, part]]) : new Map<string, TypeTerm>();
      const branch = atomOrLiteralSubtype(part, extParts)
        ? readBranch(body.trueType, bindings)
        : readBranch(body.falseType, bindings);
      for (const r of flattenUnion(branch)) {
        if (!(r.k === "atom" && r.name === "never")) results.push(r);
      }
    }
    const [only] = results;
    if (!only) return { k: "atom", name: "never", span };
    return results.length === 1 ? only : { k: "union", parts: results, span };
  }
  const holds = checkParts.every(p => atomOrLiteralSubtype(p, extParts));
  return readBranch(holds ? body.trueType : body.falseType, new Map());
}

/** Whether `body`'s `extendsType` is a generic reference containing `infer` parameters. */
export function isReferenceInferConditional(body: ts.ConditionalTypeNode): boolean {
  let ext = body.extendsType;
  while (ts.isParenthesizedTypeNode(ext)) ext = ext.type;
  if (!ts.isTypeReferenceNode(ext) || !ext.typeArguments?.length) return false;
  const hasInfer = (n: Node): boolean =>
    ts.isInferTypeNode(n) || (n.forEachChild(c => hasInfer(c) || undefined) ?? false);
  return ext.typeArguments.some(hasInfer);
}

export type ConditionalEvalOptions = {
  body: ts.ConditionalTypeNode;
  checkTerm: TypeTerm;
  distributive: boolean;
  span: Span;
  readBranch: (branch: TypeNode, bindings: ReadonlyMap<string, TypeTerm>) => TypeTerm;
  targetInfo: (ref: TypeReferenceNode) => ConditionalTargetInfo | null;
  memberInfo: (ref: Extract<TypeTerm, { k: "reference" }>) => MemberReferenceInfo | null;
};

/** Sound `TypeTerm`-level evaluation of `T extends Ref<infer A, infer B, ...> ? True : False`.
 * Matches `TypeTerm` directly by declaration identity (following type aliases and
 * declared heritage bases), takes `False` only when `T` is provably disjoint from
 * `Ref`, and refuses ambiguous or structurally overlapping cases. */
export function evaluateConditionalOnTerm(options: ConditionalEvalOptions): TypeTerm {
  const { body, checkTerm, distributive, span, readBranch, targetInfo, memberInfo } = options;
  let ext = body.extendsType;
  while (ts.isParenthesizedTypeNode(ext)) ext = ext.type;
  if (!ts.isTypeReferenceNode(ext))
    throw Error("conditional check requires a reference pattern `Ref` or `Ref<infer ...>`");
  const inferNames: string[] = [];
  for (const arg of ext.typeArguments ?? []) {
    let inner = arg;
    while (ts.isParenthesizedTypeNode(inner)) inner = inner.type;
    if (!ts.isInferTypeNode(inner))
      throw Error("conditional `infer` over a generic reference requires every type argument of the pattern to be `infer P`");
    if (inner.typeParameter.constraint)
      throw Error(`constrained \`infer ${inner.typeParameter.name.text} extends ...\` is outside the fragment`);
    const paramName = inner.typeParameter.name.text;
    if (inferNames.includes(paramName))
      throw Error(`duplicate \`infer ${paramName}\` parameter in conditional pattern is outside the fragment`);
    inferNames.push(paramName);
  }
  const target = targetInfo(ext);
  if (!target)
    throw Error(`conditional \`infer\` target ${ext.typeName.getText(ext.getSourceFile())} is not a declared generic class, interface or alias`);
  if (!target.isClassOrInterface && !target.allParamsUsed)
    throw Error(`conditional \`infer\` target alias ${target.identity.name} drops a type parameter, which cannot be inferred soundly`);
  if (target.paramCount !== inferNames.length)
    throw Error(`conditional \`infer\` target ${target.identity.name} takes ${target.paramCount} type arguments, not ${inferNames.length}`);

  type MatchOutcome =
    | { kind: "match"; args: readonly TypeTerm[] }
    | { kind: "disjoint" }
    | { kind: "ambiguous"; reason: string };

  const searchBases = (bases: readonly TypeTerm[], depth: number): { kind: "found"; args: readonly TypeTerm[] } | { kind: "none" } | { kind: "conflict" } => {
    if (depth > 16) return { kind: "conflict" };
    let found: readonly TypeTerm[] | null = null;
    for (const base of bases) {
      if (base.k !== "reference") continue;
      if (sameIdentity(base.reference.target, target.identity) && base.args.length === inferNames.length) {
        if (found && !sameTermList(found, base.args)) return { kind: "conflict" };
        found = base.args;
        continue;
      }
      const info = memberInfo(base);
      if (info && info.bases.length) {
        const sub = searchBases(info.bases, depth + 1);
        if (sub.kind === "conflict") return { kind: "conflict" };
        if (sub.kind === "found") {
          if (found && !sameTermList(found, sub.args)) return { kind: "conflict" };
          found = sub.args;
        }
      }
    }
    return found ? { kind: "found", args: found } : { kind: "none" };
  };

  const matchSingle = (member: TypeTerm, depth: number): MatchOutcome => {
    if (depth > 16) return { kind: "ambiguous", reason: "alias unfolding exceeded depth limit" };
    switch (member.k) {
      case "reference": {
        if (sameIdentity(member.reference.target, target.identity) && member.args.length === inferNames.length)
          return { kind: "match", args: member.args };
        const info = memberInfo(member);
        if (!info) return { kind: "ambiguous", reason: `no declaration shape for ${member.reference.name}` };
        if (info.unfolded) return matchSingle(info.unfolded, depth + 1);
        if (info.bases.length) {
          const inherited = searchBases(info.bases, depth + 1);
          if (inherited.kind === "found") return { kind: "match", args: inherited.args };
          if (inherited.kind === "conflict")
            return { kind: "ambiguous", reason: `${member.reference.name} inherits ${target.identity.name} at conflicting arguments` };
        }
        if (target.isLibraryWrapper)
          return { kind: "ambiguous", reason: `cannot decide disjointness from library wrapper ${target.identity.name}` };
        if (target.hasNominalMember) return { kind: "disjoint" };
        if (!info.hasStringIndex && info.props !== null) {
          const owned = new Set(info.props);
          if (target.requiredProps.some(req => !owned.has(req))) return { kind: "disjoint" };
        }
        return { kind: "ambiguous", reason: `${member.reference.name} structurally overlaps ${target.identity.name} without extending it` };
      }
      case "atom": {
        if (member.name === "unknown" || member.name === "object")
          return { kind: "ambiguous", reason: `\`${member.name}\` may or may not extend ${target.identity.name}` };
        if (!target.isLibraryWrapper && (target.hasNominalMember || target.requiredProps.length > 0))
          return { kind: "disjoint" };
        return { kind: "ambiguous", reason: `${target.identity.name} has no required member excluding \`${member.name}\`` };
      }
      case "literal":
      case "unique": {
        if (!target.isLibraryWrapper && (target.hasNominalMember || target.requiredProps.length > 0))
          return { kind: "disjoint" };
        return { kind: "ambiguous", reason: `${target.identity.name} has no required member excluding literals` };
      }
      case "function":
      case "constructor": {
        if (!target.isLibraryWrapper && (target.hasNominalMember || target.requiredProps.some(p => !FUNCTION_PROPS.has(p))))
          return { kind: "disjoint" };
        return { kind: "ambiguous", reason: `function/constructor may overlap ${target.identity.name}` };
      }
      case "array":
      case "tuple": {
        if (!target.isLibraryWrapper && (target.hasNominalMember || target.requiredProps.some(p => !ARRAY_PROPS.has(p))))
          return { kind: "disjoint" };
        return { kind: "ambiguous", reason: `array/tuple may overlap ${target.identity.name}` };
      }
      case "object": {
        if (target.isLibraryWrapper)
          return { kind: "ambiguous", reason: `cannot decide disjointness from library wrapper ${target.identity.name}` };
        if (target.hasNominalMember) return { kind: "disjoint" };
        if (member.stringIndex === null) {
          const owned = new Set(member.fields.filter(f => typeof f.name === "string").map(f => String(f.name)));
          if (target.requiredProps.some(req => !owned.has(req))) return { kind: "disjoint" };
        }
        return { kind: "ambiguous", reason: `record structurally overlaps ${target.identity.name} without nominal match` };
      }
      default:
        return { kind: "ambiguous", reason: `cannot soundly decide conditional \`infer\` over ${member.k}` };
    }
  };

  const makeBindings = (args: readonly TypeTerm[]): Map<string, TypeTerm> => {
    const map = new Map<string, TypeTerm>();
    for (let i = 0; i < inferNames.length; i++) {
      const n = inferNames[i];
      const a = args[i];
      if (n !== undefined && a !== undefined) map.set(n, a);
    }
    return map;
  };

  const parts = flattenUnion(checkTerm).filter(p => !(p.k === "atom" && p.name === "never"));
  if (distributive) {
    if (!parts.length) return { k: "atom", name: "never", span };
    const results: TypeTerm[] = [];
    for (const part of parts) {
      const outcome = matchSingle(part, 0);
      if (outcome.kind === "ambiguous")
        throw Error(`conditional \`infer\` over ${target.identity.name} is ambiguous: ${outcome.reason}`);
      const branch = outcome.kind === "match"
        ? readBranch(body.trueType, makeBindings(outcome.args))
        : readBranch(body.falseType, new Map());
      if (!(branch.k === "atom" && branch.name === "never")) results.push(branch);
    }
    const [only] = results;
    if (!only) return { k: "atom", name: "never", span };
    return results.length === 1 ? only : { k: "union", parts: results, span };
  }

  // Non-distributive conditional (e.g. `Defs[K] extends InputDefinition<infer Key, infer Val> ? ... : never`).
  if (!parts.length) {
    // In TypeScript, `never extends Ref<infer P_1, ...>` takes the true branch
    // with each `P_i` falling back to `Ref`'s parameter constraint (or `unknown`).
    const fallback = target.paramBounds.map(b => b ?? { k: "atom" as const, name: "unknown" as const, span });
    return readBranch(body.trueType, makeBindings(fallback));
  }
  // Refuse if any member is an open type parameter/binder.
  for (const part of parts) {
    if (part.k === "binder" || part.k === "parameter")
      throw Error(`conditional \`infer\` over ${target.identity.name} on an open type parameter is evaluated only at a concrete instance`);
  }
  const outcomes = parts.map(part => matchSingle(part, 0));
  if (outcomes.some(o => o.kind === "disjoint"))
    return readBranch(body.falseType, new Map());
  const ambiguous = outcomes.find((o): o is { kind: "ambiguous"; reason: string } => o.kind === "ambiguous");
  if (ambiguous)
    throw Error(`conditional \`infer\` over ${target.identity.name} is ambiguous: ${ambiguous.reason}`);
  const matched = outcomes.filter((o): o is { kind: "match"; args: readonly TypeTerm[] } => o.kind === "match");
  const [first, ...rest] = matched;
  if (!first || rest.some(m => !sameTermList(m.args, first.args)))
    throw Error(`conditional \`infer\` over ${target.identity.name} on a union of distinct instantiations is ambiguous`);
  return readBranch(body.trueType, makeBindings(first.args));
}

/** Pure `TypeTerm`-level `keyof` for records, empty objects, intersections, unions,
 * `never`, and (via `referenceKeys`) named interfaces/aliases. Returns null when
 * the key set cannot be determined directly from `term`. */
export function keyofTerm(term: TypeTerm, span: Span,
    referenceKeys?: (ref: Extract<TypeTerm, { k: "reference" }>) => TypeTerm | null,
    skipNumericKeys: boolean = false): TypeTerm | null {
  if (isEmptyObject(term)) return { k: "atom", name: "never", span };
  if (term.k === "atom" && term.name === "never")
    return { k: "union", parts: [
      { k: "atom", name: "string", span },
      { k: "atom", name: "number", span },
      { k: "atom", name: "symbol", span },
    ], span };
  if (term.k === "object") {
    if (skipNumericKeys && term.fields.some(f => typeof f.name === "string" && /^(0|[1-9][0-9]*)$/.test(f.name)))
      return null;
    const parts: TypeTerm[] = [];
    for (const f of term.fields) {
      if (typeof f.name === "string") parts.push({ k: "literal", name: "string", text: f.name, span });
      else parts.push({ k: "unique", symbol: f.name.symbol, span });
    }
    if (term.stringIndex) {
      parts.push({ k: "atom", name: "string", span });
      parts.push({ k: "atom", name: "number", span });
    }
    if (term.numberIndex && !term.stringIndex) parts.push({ k: "atom", name: "number", span });
    if (term.symbolIndex) parts.push({ k: "atom", name: "symbol", span });
    const [only] = parts;
    if (!only) return { k: "atom", name: "never", span };
    return parts.length === 1 ? only : { k: "union", parts, span };
  }
  if (term.k === "reference") return referenceKeys?.(term) ?? null;
  if (term.k === "intersection") {
    const sub: TypeTerm[] = [];
    for (const p of term.parts) {
      const k = keyofTerm(p, span, referenceKeys, skipNumericKeys);
      if (!k) return null;
      if (!(k.k === "atom" && k.name === "never")) sub.push(k);
    }
    const [only] = sub;
    if (!only) return { k: "atom", name: "never", span };
    return sub.length === 1 ? only : { k: "union", parts: sub, span };
  }
  if (term.k === "union") {
    const sub: TypeTerm[] = [];
    for (const p of term.parts) {
      const k = keyofTerm(p, span, referenceKeys, skipNumericKeys);
      if (!k) return null;
      sub.push(k);
    }
    return reduceLiteralIntersection(sub, span);
  }
  return null;
}

/** Pure `TypeTerm`-level indexed access `object[keys]` (used during `instantiateAt`
 * when operands come from substituted `TypeTerm`s). Returns null when it cannot be
 * resolved directly. */
export function projectTerm(object: TypeTerm, keys: TypeTerm, span: Span,
    unfold?: (ref: Extract<TypeTerm, { k: "reference" }>) => TypeTerm | null): TypeTerm | null {
  const keyList = flattenUnion(keys).filter(k => !(k.k === "atom" && k.name === "never"));
  if (!keyList.length) return { k: "atom", name: "never", span };
  const combine = (parts: TypeTerm[]): TypeTerm => {
    const flat = parts.flatMap(flattenUnion).filter(p => !(p.k === "atom" && p.name === "never"));
    const [only] = flat;
    if (!only) return { k: "atom", name: "never", span };
    return flat.length === 1 ? only : { k: "union", parts: flat, span };
  };
  const go = (obj: TypeTerm, depth: number): TypeTerm | null => {
    if (depth > 32) return null;
    switch (obj.k) {
      case "union": {
        const res: TypeTerm[] = [];
        for (const p of obj.parts) {
          const projected = go(p, depth + 1);
          if (!projected) return null;
          res.push(projected);
        }
        return combine(res);
      }
      case "intersection": {
        const res: TypeTerm[] = [];
        for (const p of obj.parts) {
          const projected = go(p, depth + 1);
          if (!projected) return null;
          res.push(projected);
        }
        return { k: "intersection", parts: res, span };
      }
      case "array":
        if (keyList.every(k => k.k === "atom" && k.name === "number")) return obj.element;
        return null;
      case "tuple": {
        const out: TypeTerm[] = [];
        for (const key of keyList) {
          if (key.k === "atom" && key.name === "number") {
            out.push(...obj.required, ...obj.optional.map(t => optionalTerm(t, span)), ...(obj.rest ? [obj.rest] : []));
          } else if (key.k === "literal" && key.name === "number" && /^[0-9]+$/.test(key.text)) {
            const i = Number(key.text);
            const pos = obj.required[i] ?? obj.optional[i - obj.required.length];
            if (pos) out.push(i < obj.required.length ? pos : optionalTerm(pos, span));
            else if (obj.rest) out.push(obj.rest);
            else return null;
          } else {
            return null;
          }
        }
        return combine(out);
      }
      case "object": {
        const out: TypeTerm[] = [];
        for (const key of keyList) {
          if (key.k === "literal" && key.name === "string") {
            const field = obj.fields.find(f => f.name === key.text);
            if (field) out.push(field.optional ? optionalTerm(field.type, span) : field.type);
            else if (obj.stringIndex) out.push(obj.stringIndex.value);
            else return null;
          } else if (key.k === "atom" && key.name === "string" && obj.stringIndex) {
            out.push(obj.stringIndex.value);
            for (const f of obj.fields) {
              if (typeof f.name === "string") out.push(f.optional ? optionalTerm(f.type, span) : f.type);
            }
          } else if (key.k === "atom" && key.name === "number" && (obj.numberIndex ?? obj.stringIndex)) {
            const idx = obj.numberIndex ?? obj.stringIndex;
            if (idx) out.push(idx.value);
          } else {
            return null;
          }
        }
        return combine(out);
      }
      case "reference": {
        const next = unfold?.(obj);
        return next ? go(next, depth + 1) : null;
      }
      default:
        return null;
    }
  };
  return go(object, 0);
}
