/** Types TypeScript computes from other types: `typeof x`, `keyof T`, `T[K]`,
 * template literal types and applications of aliases computed from their
 * parameters (PROGRAM-TYPING.md, "Computed types"). Their meaning is the type
 * TypeScript computes, which the checker gives; this module states it as the
 * equivalent type term the fragment already has, or refuses it with the
 * reason no such term exists. Nothing here is a second reading of type
 * syntax: a type the result names is read by `type-term.mts`, where it is
 * declared. What is read from the checker's types is only what has no
 * syntax: a union of literals and primitives, and the record an object
 * literal's inferred type is. */
import { childOf, childrenOf, isStatic } from "./syntax.mts";
import { SignatureKind, SymbolFlags, TypeFlags, type Checker, type Type } from "typescript/unstable/sync";
import * as ts from "typescript/unstable/ast";
import type { Node, TypeAliasDeclaration, TypeNode, TypeReferenceNode } from "typescript/unstable/ast";
import type { Span } from "./span.mts";
import type { TypeTerm } from "./declaration-types.mts";
import { computedAlias, computedForm, numericKey, optionalTerm } from "./type-term.mts";

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
  /** The reader of type syntax inside `alias`'s equation with its parameters
   * read as `args`, in the alias's own scope. */
  applied(alias: TypeAliasDeclaration, args: readonly TypeTerm[]): (node: TypeNode) => TypeTerm;
  /** A generic alias's equation at a reference's arguments, when it is an
   * array, a tuple or another alias's application; null otherwise. */
  equation(reference: Extract<TypeTerm, { k: "reference" }>): TypeTerm | null;
  /** The identity of the symbol a `unique symbol` type names: the index of
   * the `unique symbol` constant or well-known symbol declaring it among the
   * listed symbols, as a computed key `[k]` naming it is read. Throws the
   * reason where the symbol it holds is not known. */
  unique(type: Type): number;
};

/** The number's decimal spelling, as a literal type's text is written. */
function numberText(value: number): string | null {
  return Number.isFinite(value) ? String(value) : null;
}

/** A bigint literal type's value, which the checker sends as its decimal
 * spelling, a bigint, or a sign and digits. */
function bigintValue(value: unknown): string | null {
  if (typeof value === "bigint" || typeof value === "string") return String(value);
  if (value && typeof value === "object" && "base10Value" in value && typeof value.base10Value === "string")
    return ("negative" in value && value.negative === true ? "-" : "") + value.base10Value;
  return null;
}

/** `type` as a union of the fragment's primitive families and literals, when
 * it is exactly one: each part a literal (string, number, bigint, Boolean), a
 * primitive family, `null`, `undefined`, `void`, `unknown` or `never`, and,
 * where `unique` identifies symbols, a unique symbol. An enum literal, an
 * object, a type parameter or a string pattern is not one, and the answer is
 * null. */
export function literalUnion(type: Type, span: Span, unique?: (part: Type) => number): TypeTerm | null {
  const parts = type.isUnionType() ? type.getTypes() : [type];
  const terms: TypeTerm[] = [];
  const atom = (name: Extract<TypeTerm, { k: "atom" }>["name"]): TypeTerm => ({ k: "atom", name, span });
  for (const part of parts) {
    const f = part.flags;
    if (f & TypeFlags.EnumLiteral) return null;
    if (part.isStringLiteralType()) terms.push({ k: "literal", name: "string", text: part.value, span });
    else if (part.isNumberLiteralType()) {
      const text = numberText(part.value);
      if (text === null) return null;
      terms.push({ k: "literal", name: "number", text, span });
    } else if (part.isBigIntLiteralType()) {
      const text = bigintValue(part.value);
      if (text === null) return null;
      terms.push({ k: "literal", name: "bigint", text, span });
    } else if (part.isBooleanLiteralType())
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
  const type = checker.getTypeFromTypeNode(node);
  if (!type || type.isErrorType()) throw Error(`TypeScript computes no type for this ${form}: it is not valid TypeScript`);
  const literals = literalUnion(type, span, context.unique);
  if (literals) return literals;
  const computed = describe(checker, type);
  if (ts.isTypeReferenceNode(node)) return aliasApplication(context, node, span, read, computed);
  if (ts.isTypeQueryNode(node)) return typeQuery(context, node, type, span);
  if (ts.isIndexedAccessTypeNode(node)) return indexedAccess(context, node, type, span, read);
  // `keyof` of the type literal its operand reads as, where TypeScript
  // defers it over a type parameter (an alias's, read at its argument).
  if (ts.isTypeOperatorNode(node) && node.operator === ts.SyntaxKind.KeyOfKeyword) {
    const keys = keysOf(read(node.type), span);
    if (keys) return keys;
  }
  if (ts.isTemplateLiteralTypeNode(node) || type.isTemplateLiteralType() || type.isStringMappingType())
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
  const parameters = alias.typeParameters ?? [];
  const written = node.typeArguments ?? [];
  if (written.length !== parameters.length)
    throw Error(`the computed type alias ${alias.name.text} is applied at a default type argument, outside the fragment`);
  let body = alias.type;
  while (ts.isParenthesizedTypeNode(body)) body = body.type;
  return computedType(context, body, span, context.applied(alias, written.map(read)));
}

/** `keyof` of a type literal: the union of its property names' string
 * literals, as TypeScript computes it; null where the keys are not only such
 * names (an index signature, a symbol or numeric key, a type that is not a
 * literal). */
function keysOf(object: TypeTerm, span: Span): TypeTerm | null {
  if (object.k !== "object" || object.stringIndex || object.numberIndex || object.symbolIndex || object.prototype)
    return null;
  const parts: TypeTerm[] = [];
  for (const field of object.fields) {
    if (typeof field.name !== "string") return null;
    // A numeric name's key is its literal as written, `1` or `"1"`, which
    // the term no longer tells apart.
    if (numericKey(field.name) === field.name) return null;
    parts.push({ k: "literal", name: "string", text: field.name, span });
  }
  const [only] = parts;
  if (!only) return { k: "atom", name: "never", span };
  return parts.length === 1 ? only : { k: "union", parts, span };
}

/** Why `type` is not a union of literals and primitives: its first part that
 * is not one. */
function inexpressible(checker: Checker, type: Type): string {
  const parts = type.isUnionType() ? type.getTypes() : [type];
  const part = parts.find(p => literalUnion(p, [0, 0]) === null) ?? type;
  const what = part.flags & TypeFlags.EnumLiteral ? "an enum member, outside the fragment"
    : "not a literal or a primitive";
  return `whose part ${checker.typeToString(part)} is ${what}`;
}

/** Whether `type` still names a type parameter: TypeScript defers it. */
function generic(type: Type): boolean {
  if (type.isTypeParameter() || type.isIndexType() || type.isIndexedAccessType() || type.isConditionalType() ||
      type.isSubstitutionType()) return true;
  return type.isUnionType() && type.getTypes().some(generic);
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
    !!d && !ts.isInterfaceDeclaration(d) && !ts.isTypeAliasDeclaration(d));
  const [first] = nodes;
  if (!first) throw Error(`${what} names nothing TypeScript declares`);
  // An annotation's `typeof E` is the enum's object type, which the parser
  // reads (PROGRAM-TYPING.md, "Enums"); the declaration reader does not read enums.
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
    type.isUnionType() && type.getTypes().some(t => (t.flags & TypeFlags.Undefined) !== 0);
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
export function inferredTerm(checker: Checker, type: Type, span: Span, depth = 0): TypeTerm | null {
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
  const indexes: { stringIndex: { readonly: boolean; value: TypeTerm; span: Span } | null;
    numberIndex?: { readonly: boolean; value: TypeTerm; span: Span };
    symbolIndex?: { readonly: boolean; value: TypeTerm; span: Span } } = { stringIndex: null };
  for (const info of checker.getIndexInfosOfType(type)) {
    const value = inferredTerm(checker, info.valueType, span, depth + 1);
    if (!value) return null;
    const index = { readonly: info.isReadonly, value, span };
    const key = info.keyType.flags;
    if (key & TypeFlags.String && !indexes.stringIndex) indexes.stringIndex = index;
    else if (key & TypeFlags.Number && !indexes.numberIndex) indexes.numberIndex = index;
    else if (key & TypeFlags.ESSymbol && !indexes.symbolIndex) indexes.symbolIndex = index;
    else return null;
  }
  return { k: "object", fields, ...indexes, calls: [], span };
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
  const project = (object: TypeTerm): TypeTerm => {
    switch (object.k) {
      case "union": return union(object.parts.map(project));
      // An intersection's member at a key is the meet of its operands'
      // members there: `(A[] & B[])[number]` is `A & B`.
      case "intersection": return { k: "intersection", parts: object.parts.map(project), span };
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
        const alias = aliasOf(node.objectType);
        if (alias && object.args.length === 0)
          return project(context.annotation(alias.type, alias, []));
        // A generic alias of an array, a tuple or another alias: its
        // equation at the reference's arguments.
        const equation = object.args.length ? context.equation(object) : null;
        if (equation) return project(equation);
        return member();
      }
    }
    throw Error(`the indexed access ${computed} has no member, element or position at its key`);
  };
  // The type alias without parameters a type reference names.
  const aliasOf = (reference: TypeNode): ts.TypeAliasDeclaration | null => {
    if (!ts.isTypeReferenceNode(reference) || !ts.isIdentifier(reference.typeName)) return null;
    const nodes = (checker.getSymbolAtLocation(reference.typeName)?.declarations ?? []).map(d => d.resolve());
    const [only] = nodes;
    return nodes.length === 1 && only && ts.isTypeAliasDeclaration(only) && !only.typeParameters?.length
      ? only : null;
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
    // TypeScript defers an access it cannot compute before an instance.
    if (generic(type))
      throw Error(`the indexed access ${computed} over a type parameter is computed only at an instance`);
    throw error;
  }
}
