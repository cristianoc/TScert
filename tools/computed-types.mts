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
import type { TypeTerm } from "./declaration-types.mts";
import { computedAlias, computedForm, numericKey, optionalTerm } from "./type-term.mts";
import { passToolFailure } from "./thrown.mts";

/** What the evaluator reads with: the project's checker, and the reader of a
 * declaration's own annotation, in that declaration's scope, with the binders
 * of the functions enclosing it (`binders`), or of the value a name denotes, as
 * an import of it is read. */
export type ComputedContext = {
  checker: Checker;
  annotation(node: TypeNode, at: Node, binders: string[]): TypeTerm;
  /** The type of the value `declarations` bind, read as an imported one's
   * is, with its binders (a generic value has some). */
  value(declarations: readonly Node[], what: string): { typeParams: readonly unknown[]; type: TypeTerm };
  /** The type alias a reference names, as TypeScript resolves it, if it
   * names one. */
  alias(reference: TypeReferenceNode): TypeAliasDeclaration | null;
  /** The declaration named by the current projected reference. */
  referenceAlias(reference: Extract<TypeTerm, { k: "reference" }>): TypeAliasDeclaration | null;
  /** The reader of type syntax inside `alias`'s declaration with its
   * parameters read as `args`, in the alias's own scope, a computed form
   * naming them evaluated by TypeScript at the application `use`. */
  applied(alias: TypeAliasDeclaration, args: readonly TypeTerm[], use: Node): (node: TypeNode) => TypeTerm;
  /** A generic alias's equation at a reference's arguments, when it is an
   * array, a tuple or another alias's application; null otherwise. */
  equation(reference: Extract<TypeTerm, { k: "reference" }>): TypeTerm | null;
  /** Throws where `node` names a type declared in a block one of whose
   * captured binders a nearer declaration hides there (SOURCE-CONTRACTS.md,
   * "Block-scoped type declarations"): TypeScript's evaluation would read
   * it past that refusal. */
  captures(node: TypeNode): void;
  /** The identity of the symbol a `unique symbol` type names: the index of
   * the `unique symbol` constant or well-known symbol declaring it among the
   * listed symbols, as a computed key `[k]` naming it is read. Throws the
   * reason where the symbol it holds is not known. */
  unique(type: Type): number;
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
    read: (node: TypeNode) => TypeTerm): TypeTerm {
  const { checker } = context;
  const form = computedForm(node) ?? "a computed type";
  context.captures(node);
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
    read: (node: TypeNode) => TypeTerm, computed: string): TypeTerm {
  const alias = context.alias(node);
  if (!alias || !computedAlias(alias, context.alias))
    throw Error(`${computed} is not an application of a type alias TypeScript computes`);
  // An omitted argument is its parameter's default, read at the earlier
  // arguments.
  const applied = parameterMembers(context, alias, node, read, new Map());
  if (!applied) throw Error(`${computed} omits an argument of ${alias.name.text} that has no default`);
  let body = alias.type;
  while (ts.isParenthesizedTypeNode(body)) body = body.type;
  if (ts.isConditionalTypeNode(body)) return distributed(context, node, alias, body, span, computed, applied.members);
  const atArguments = context.applied(alias, applied.args, node);
  // An application of an alias that is no computed alias, one of whose
  // arguments is computed (`Pick<T, Exclude<keyof T, K>>`), is that alias
  // at the arguments, each evaluated at this reference.
  const target = ts.isTypeReferenceNode(body) ? context.alias(body) : null;
  if (ts.isTypeReferenceNode(body) && !(target && computedAlias(target, context.alias))) return atArguments(body);
  return computedType(context, body, span, atArguments);
}

/** A union member as written: its type node, the reader of the scope it
 * is written in, and the members the parameters it may name stand for. */
type Member = { node: TypeNode; read: (node: TypeNode) => TypeTerm; params: ReadonlyMap<Node, Member> };

/** The members `alias`'s parameters stand for at `reference`: each written
 * argument where it is written, each omitted one its default, read at the
 * earlier ones; null where one has neither. */
function parameterMembers(context: ComputedContext, alias: TypeAliasDeclaration, reference: TypeReferenceNode,
    read: (node: TypeNode) => TypeTerm, params: ReadonlyMap<Node, Member>): { args: TypeTerm[]; members: Map<Node, Member> } | null {
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
function unionMembers(context: ComputedContext, node: TypeNode, read: (node: TypeNode) => TypeTerm,
    seen: Set<Node> = new Set(), params: ReadonlyMap<Node, Member> = new Map()): Member[] {
  while (ts.isParenthesizedTypeNode(node)) node = node.type;
  if (ts.isUnionTypeNode(node)) return node.types.flatMap(t => unionMembers(context, t, read, seen, params));
  if (ts.isTypeReferenceNode(node) && ts.isIdentifier(node.typeName) && !node.typeArguments?.length) {
    const declarations = (context.checker.getSymbolAtLocation(node.typeName)?.declarations ?? []).map(d => d.resolve());
    const standing = declarations.map(d => d && params.get(d)).find(m => m !== undefined);
    if (standing) return unionMembers(context, standing.node, standing.read, seen, standing.params);
  }
  const alias = ts.isTypeReferenceNode(node) ? context.alias(node) : null;
  // A computed alias has no equation to read members from.
  const computed = (n: Node): boolean => computedAlias(n, context.alias);
  if (!alias || !ts.isTypeReferenceNode(node) || seen.has(alias) || enclosingBinders(alias).length || computed(alias))
    return [{ node, read, params }];
  const applied = parameterMembers(context, alias, node, read, params);
  if (!applied) return [{ node, read, params }];
  return unionMembers(context, alias.type, context.applied(alias, applied.args, node), new Set([...seen, alias]), applied.members);
}

/** An application of an alias whose equation is a conditional type
 * distributing over its parameter, `Extract<T, U>`, which is
 * `T extends U ? T : never`: where TypeScript decides it for each member of
 * the argument's union, and its result is a union of whole members, it is
 * the union of those members, each read as written. Where TypeScript computes
 * a union of literals and primitives for it, that union was taken already. */
function distributed(context: ComputedContext, node: TypeReferenceNode, alias: TypeAliasDeclaration,
    body: ts.ConditionalTypeNode, span: Span, computed: string, args: ReadonlyMap<Node, Member>): TypeTerm {
  const { checker } = context;
  const type = checker.getTypeFromTypeNode(node);
  if (!type || generic(type))
    throw Error(`a conditional type over a type parameter, ${computed}, is computed only at an instance`);
  const check = body.checkType;
  const index = ts.isTypeReferenceNode(check) && ts.isIdentifier(check.typeName) && !check.typeArguments?.length
    ? (alias.typeParameters ?? []).findIndex(p => ts.isIdentifier(check.typeName) && p.name.text === check.typeName.text)
    : -1;
  const parameter = (alias.typeParameters ?? [])[index];
  const decided = parameter && args.get(parameter);
  if (!decided)
    throw Error(`the conditional type ${alias.name.text} decides a type other than one of its parameters, ` +
      `${computed}: it distributes over no union`);
  const argument = decided.node;
  const members = unionMembers(context, argument, decided.read, new Set(), decided.params);
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
    const signatures = declared.some(f => !f.body) ? declared.filter(f => !f.body) : declared;
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

/** Why `type` is not a union of literals and primitives: its first part that
 * is not one. */
function inexpressible(checker: Checker, type: Type): string {
  const parts = isUnionType(type) ? type.getTypes() : [type];
  const part = parts.find(p => literalUnion(p, [0, 0]) === null) ?? type;
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
    if (!ts.isClassDeclaration(first) || !first.members.some(isStatic)) return value.type;
    // A class value's static fields are own data properties of it, which its
    // type states; its static methods are bindings of their own, which no
    // member of its type states.
    const statics = first.members.filter(isStatic).flatMap(member => {
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
 * the index signatures a spread copied into it. Null for anything else: a
 * method, a symbol-keyed or `const`-asserted property, a property a spread
 * copied from a declared type, an array, a function. */
export function inferredTerm(checker: Checker, type: Type, span: Span, depth: number = 0): TypeTerm | null {
  const literals = literalUnion(type, span);
  if (literals) return literals;
  if (depth > 8 || !(type.flags & TypeFlags.Object) ||
      checker.getSignaturesOfType(type, SignatureKind.Call).length ||
      checker.getSignaturesOfType(type, SignatureKind.Construct).length) return null;
  const fields: Extract<TypeTerm, { k: "object" }>["fields"] = [];
  for (const property of checker.getPropertiesOfType(type)) {
    const declaration = property.valueDeclaration?.resolve();
    if (!declaration || !(ts.isPropertyAssignment(declaration) || ts.isShorthandPropertyAssignment(declaration)) ||
        !ts.isIdentifier(declaration.name) || declaration.name.text !== property.name ||
        (property.flags & SymbolFlags.Optional) !== 0 || underConstAssertion(declaration)) return null;
    const value = checker.getTypeOfSymbol(property);
    const term = value ? inferredTerm(checker, value, span, depth + 1) : null;
    if (!term) return null;
    fields.push({ name: property.name, optional: false, readonly: false, type: term, span });
  }
  let stringIndex: { readonly: boolean; value: TypeTerm; span: Span } | null = null;
  let numberIndex: { readonly: boolean; value: TypeTerm; span: Span } | null = null;
  let symbolIndex: { readonly: boolean; value: TypeTerm; span: Span } | null = null;
  for (const info of checker.getIndexInfosOfType(type)) {
    const value = inferredTerm(checker, info.valueType, span, depth + 1);
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
function indexedAccess(context: ComputedContext, node: ts.IndexedAccessTypeNode, type: Type, span: Span,
    read: (node: TypeNode) => TypeTerm): TypeTerm {
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
      case "union": return union(object.parts.map(part => project(part, depth + 1)));
      // An intersection's member at a key is the meet of its operands'
      // members there: `(A[] & B[])[number]` is `A & B`.
      case "intersection": return { k: "intersection", parts: object.parts.map(part => project(part, depth + 1)), span };
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
        if (parts.every((p): p is TypeTerm => p !== null)) return union(parts);
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
            return project(context.annotation(alias.type, alias, []), depth + 1);
          } finally {
            projecting.delete(alias);
          }
        }
        // A generic alias of an array, a tuple or another alias: its
        // equation at the reference's arguments.
        const equation = object.args.length ? context.equation(object) : null;
        if (equation) return project(equation, depth + 1);
        return member();
      }
    }
    throw Error(`the indexed access ${computed} has no member, element or position at its key`);
  };
  // A member of a named type: its declaration's annotation, when that is
  // exactly what TypeScript computes and names no type parameter.
  const member = (): TypeTerm => {
    const objectType = checker.getTypeFromTypeNode(node.objectType);
    const [key] = keyList;
    if (!objectType || keyList.length !== 1 || key?.k !== "literal" || key.name !== "string")
      throw Error(`the indexed access ${computed} into a named type needs one string key`);
    const property = checker.getPropertyOfType(objectType, key.text);
    const nodes = (property?.declarations ?? []).map(d => d.resolve()).filter((d): d is Node => !!d);
    const [only] = nodes;
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
