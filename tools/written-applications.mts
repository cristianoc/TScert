/** The type applications written in source syntax, each with the scope it
 * is written in (SOURCE-CONTRACTS.md, "Written applications"). An
 * application `D<σ⃗>` obliges each argument, completed with the defaults, to
 * meet its parameter's bound under the scope's assumptions, whatever term a
 * reader states for the type it is written in: the obligations are read
 * from the syntax here, never from a denotation. */
import * as ts from "typescript/unstable/ast";
import type { Node, TypeNode } from "typescript/unstable/ast";
import type { Span } from "./span.mts";
import type { SourceTypeParameter, TypeTerm, WrittenApplication } from "./declaration-types.mts";
import { visitType } from "./type-term.mts";
import { childrenOf, nameOf } from "./syntax.mts";

/** What the sweep needs from the declaration graph. */
export type SweepContext = {
  /** The declarations TypeScript binds a written name to (empty when it
   * binds none). */
  declarationsOf(name: ts.Identifier): readonly Node[];
  /** The declarations of the symbol a written name denotes, aliases
   * (re-exports, renames, type-only imports, `export =`) followed to their
   * target; null where it denotes no symbol. */
  resolve(name: ts.Identifier): readonly Node[] | null;
  /** The type declaration a written name denotes, with its merged parts
   * (the first part identifies it), when it denotes an alias, an interface
   * or a class outside the standard library, or a library type with a
   * bounded parameter; null for any other name. */
  declaration(name: ts.Identifier): readonly Node[] | null;
  /** Whether `node` is in the standard library, whose declarations are not
   * swept. */
  library(node: Node): boolean;
  /** The term of `node` read where it is written, a type parameter read as
   * `binder` names it (undefined for one not in scope). */
  read(node: TypeNode, binder: (declaration: ts.TypeParameterDeclaration) => string | undefined): TypeTerm;
  /** The written reference's edge to the declaration it names. */
  reference(name: ts.Identifier, args: readonly TypeNode[]): WrittenApplication["reference"];
  /** The declarations a member selection depends on: the top-level
   * declarations holding the members of `object`'s type at `key`'s literal
   * keys, or at every key where `key` is null or not a union of literals. */
  members(object: TypeNode, key: TypeNode | null): readonly Node[];
  /** Whether a declaration is an alias TypeScript computes from its
   * parameters, whose equation may select members of its arguments. */
  computed(declaration: Node): boolean;
  /** The declarations of the module a specifier names; null where none. */
  moduleOf(specifier: ts.StringLiteral): readonly Node[] | null;
  /** The module a file is, as identities name it. */
  module(file: ts.SourceFile): string;
  /** The client file, whose spans the verifier reports. */
  client: ts.SourceFile;
};

/** A written application whose obligation cannot be stated: refused where
 * it is written, at `span` in the client file, or null elsewhere. */
export class SweepError extends Error {
  readonly span: Span | null;
  constructor(span: Span | null, message: string) {
    super(message);
    this.span = span;
  }
}

/** A binder in force: its fresh name and the term of its assumption, read
 * in its group's scope, or null for none. */
type Binder = { node: Node; name: string; bound: () => TypeTerm | null };
type Env = { names: Map<Node, string>; levels: Binder[][] };

/** Every written application in `roots` and in the declarations they reach
 * by name (`typeof` included), each user declaration once with all its
 * merged parts; standard library declarations are not swept. An
 * application is listed when its target has a bounded parameter: any other
 * obliges each argument to meet `top`, which every type does. A function
 * body or an initializer is swept only in the client file. */
export function writtenApplications(context: SweepContext, roots: readonly Node[]): WrittenApplication[] {
  const found: WrittenApplication[] = [];
  const listed = new Set<Node>();
  const swept = new Set<Node>();
  const queue: Node[] = [];
  // Each declaration reached is swept itself (a member, a property, a
  // method, a variable's declarator, a type), its annotations and type
  // syntax, with the binders of its enclosing declarations in scope
  // (`enclosing`); a module or a namespace contributes nothing by itself,
  // only the members a further step selects. The client file's code is
  // swept as a root; its interfaces and aliases, and their members, where
  // something reaches them.
  const reach = (nodes: readonly Node[], use: Node): void => {
    for (const node of nodes) {
      if (context.library(node) || (node.getSourceFile() === context.client && !withinTypeDeclaration(node) &&
          !ts.isSourceFile(node)))
        continue;
      const determined = determining(node);
      // Its type is its written annotations: one inferred from its code is
      // not read.
      if ("inferred" in determined) {
        const at = determined.inferred;
        const file = at.getSourceFile();
        throw refusal(use, `the type of ${at.getText(file).split("\n")[0]} in ${site(at)} is inferred from ` +
          "its code, which no annotation states: a contract read through an unannotated declaration is refused");
      }
      for (const part of determined.nodes)
        if (!swept.has(part)) {
          swept.add(part);
          queue.push(part);
        }
    }
  };
  // The written annotations that determine a declaration's exposed type
  // (SOURCE-FRAGMENT.md, refused on principle), by its kind; the
  // declaration whose type is inferred where there are none.
  type Determined = { nodes: Node[] } | { inferred: Node };
  const all = (parts: readonly Determined[]): Determined => {
    const nodes: Node[] = [];
    for (const part of parts) {
      if ("inferred" in part) return part;
      nodes.push(...part.nodes);
    }
    return { nodes };
  };
  const seenModules = new Set<Node>();
  const determining = (d: Node): Determined => {
    const none: Determined = { nodes: [] };
    // A type's declaration is type syntax throughout; a type parameter's
    // bound is its owner's.
    if (ts.isInterfaceDeclaration(d) || ts.isTypeAliasDeclaration(d)) return { nodes: [d] };
    if (ts.isTypeParameterDeclaration(d)) return { nodes: [d] };
    // An enum member's type is its value.
    if (ts.isEnumDeclaration(d) || ts.isEnumMember(d)) return none;
    // A variable or a binding element: its own annotation, or its enclosing
    // pattern's; a `const` initialized by a literal naming nothing.
    if (ts.isVariableDeclaration(d) || ts.isBindingElement(d) || ts.isParameterDeclaration(d)) {
      let at: Node | undefined = d;
      while (at && ts.isBindingElement(at)) at = at.parent?.parent;
      if (at && (ts.isVariableDeclaration(at) || ts.isParameterDeclaration(at)) && at.type) return { nodes: [at.type] };
      if (at && ts.isVariableDeclaration(at) && at.initializer && constant(at) && literal(at.initializer)) return none;
      return { inferred: d };
    }
    if (ts.isPropertyDeclaration(d) || ts.isPropertySignatureDeclaration(d))
      return d.type ? { nodes: [d.type] } : { inferred: d };
    // A property assignment: the annotations of its value.
    if (ts.isPropertyAssignment(d)) return value(d.initializer, d);
    if (ts.isShorthandPropertyAssignment(d)) return { inferred: d };
    // An accessor: the getter's result or the setter's parameter, either
    // supplying the pair's type.
    if (ts.isGetAccessorDeclaration(d) || ts.isSetAccessorDeclaration(d)) {
      const typed = [d, ...pairOf(d)].map(a => ts.isGetAccessorDeclaration(a) ? a.type
        : ts.isSetAccessorDeclaration(a) ? a.parameters[0]?.type : undefined).find((t): t is TypeNode => !!t);
      return typed ? { nodes: [typed] } : { inferred: d };
    }
    // A function: its overload signatures if it has any (each a declaration
    // of its own), else its parameters' and its result's annotations.
    if (ts.isFunctionDeclaration(d) || ts.isMethodDeclaration(d) || ts.isFunctionExpression(d) ||
        ts.isArrowFunction(d) || ts.isMethodSignatureDeclaration(d) || ts.isCallSignatureDeclaration(d) ||
        ts.isConstructSignatureDeclaration(d)) {
      if ("body" in d && d.body && overloaded(d)) return none;
      return signature(d);
    }
    if (ts.isConstructorDeclaration(d))
      return overloaded(d) && d.body ? none : d.parameters.every(p => !!p.type) ? { nodes: [...d.parameters] } : { inferred: d };
    if (ts.isIndexSignatureDeclaration(d)) return { nodes: [d] };
    // A class: its heritage, its type parameters and every member by its
    // kind; a static block is code.
    if (ts.isClassDeclaration(d) || ts.isClassExpression(d))
      return all([{ nodes: [...(d.typeParameters ?? []), ...(d.heritageClauses ?? [])] },
        ...d.members.filter(m => !ts.isClassStaticBlockDeclaration(m) && !ts.isSemicolonClassElement(m)).map(determining)]);
    // A namespace or a module: every exported member, `export =` meaning its
    // target.
    if (ts.isSourceFile(d) || ts.isModuleDeclaration(d)) {
      if (seenModules.has(d)) return none;
      seenModules.add(d);
      return all(exportsOf(d).map(determining));
    }
    return { inferred: d };
  };
  const signature = (d: Node): Determined => {
    const parameters = "parameters" in d && Array.isArray(d.parameters) ? d.parameters : [];
    const typed = "type" in d && !!d.type;
    if (!typed || !parameters.every(p => ts.isParameterDeclaration(p) && !!p.type)) return { inferred: d };
    return { nodes: [d] };
  };
  // A property's value: a literal naming nothing; a function's signature;
  // an object literal's properties, each by its kind; an assertion's type.
  const value = (e: Node, d: Node): Determined => {
    if (literal(e)) return { nodes: [] };
    if (ts.isParenthesizedExpression(e)) return value(e.expression, d);
    if (ts.isFunctionExpression(e) || ts.isArrowFunction(e)) return signature(e);
    if ((ts.isAsExpression(e) || ts.isSatisfiesExpression(e)) && !ts.isSatisfiesExpression(e)) return { nodes: [e.type] };
    if (ts.isObjectLiteralExpression(e)) return all(e.properties.map(determining));
    return { inferred: d };
  };
  const exportsOf = (d: ts.SourceFile | ts.ModuleDeclaration): Node[] => {
    const statements = ts.isSourceFile(d) ? d.statements
      : d.body && ts.isModuleBlock(d.body) ? d.body.statements : [];
    const found: Node[] = [];
    for (const statement of statements) {
      const exported = childrenOf(statement, "modifiers").some(m => m.kind === ts.SyntaxKind.ExportKeyword);
      if (ts.isExportAssignment(statement) && ts.isIdentifier(statement.expression))
        found.push(...(context.resolve(statement.expression) ?? [statement]));
      else if (ts.isExportDeclaration(statement)) {
        const clause = statement.exportClause;
        if (clause && ts.isNamedExports(clause))
          for (const specifier of clause.elements)
            found.push(...(ts.isIdentifier(specifier.name) ? context.resolve(specifier.name) ?? [specifier] : [specifier]));
        else if (statement.moduleSpecifier && ts.isStringLiteral(statement.moduleSpecifier))
          found.push(...(context.moduleOf(statement.moduleSpecifier) ?? [statement]));
      } else if (exported && ts.isVariableStatement(statement))
        found.push(...statement.declarationList.declarations);
      else if (exported) found.push(statement);
    }
    return found.filter(n => !context.library(n));
  };
  const fresh = (node: ts.TypeParameterDeclaration, suffix = ""): string => {
    const file = node.getSourceFile();
    return `${node.name.text}@${context.module(file)}:${node.getStart(file)}${suffix}`;
  };
  const resolve = (env: Env) => (declaration: ts.TypeParameterDeclaration): string | undefined =>
    env.names.get(declaration);
  // A binder group: all its names are in scope in all its bounds.
  const group = (env: Env, parameters: readonly ts.TypeParameterDeclaration[]): Env => {
    const names = new Map(env.names);
    for (const p of parameters) names.set(p, fresh(p));
    const inner: Env = { names, levels: env.levels };
    const level: Binder[] = parameters.map(p => {
      const name = names.get(p) ?? fresh(p);
      return { node: p, name, bound: () => p.constraint ? context.read(p.constraint, resolve(inner)) : null };
    });
    return { names, levels: [...env.levels, level] };
  };
  const site = (node: Node): string => {
    let at: Node | undefined = node;
    while (at && !(ts.isTypeAliasDeclaration(at) || ts.isInterfaceDeclaration(at) || ts.isClassDeclaration(at) ||
        ts.isFunctionDeclaration(at) || ts.isVariableDeclaration(at)))
      at = at.parent;
    const name = at && "name" in at && at.name && ts.isIdentifier(at.name) ? at.name.text : "the module";
    return `${context.module(node.getSourceFile())}#${name}`;
  };
  // The application `name<args>` written at `node`.
  const application = (node: Node, name: ts.Identifier, args: readonly TypeNode[], env: Env): void => {
    const target = context.declaration(name);
    if (!target) return;
    reach(target, node);
    if (listed.has(node)) return;
    listed.add(node);
    const [first] = target;
    const parameters = first && "typeParameters" in first ? childParameters(first) : [];
    if (!parameters.some(p => p.constraint)) return;
    const read = resolve(env);
    const file = node.getSourceFile();
    const span: Span | null = file === context.client ? [node.getStart(file), node.end] : null;
    try {
      const terms = args.map(arg => ts.isInferTypeNode(arg)
        ? { k: "binder" as const, name: env.names.get(arg.typeParameter) ?? fresh(arg.typeParameter),
            span: spanOf(arg) }
        : context.read(arg, read));
      found.push({ scope: pruned(env, terms), reference: context.reference(name, args), args: terms, span,
        site: site(node) });
    } catch (error) {
      if (error instanceof SweepError) throw error;
      throw new SweepError(span, `the written application ${node.getText(file)} in ${site(node)}: ` +
        (error instanceof Error ? error.message : String(error)));
    }
  };
  const refusal = (node: Node, message: string): SweepError => {
    const file = node.getSourceFile();
    return new SweepError(file === context.client ? spanOf(node) : null,
      `${node.getText(file)} in ${site(node)}: ${message}`);
  };
  const visit = (node: Node, env: Env, client: boolean, root = false): void => {
    // A client's interface or alias is swept where something names it.
    if (client && node.parent && (ts.isInterfaceDeclaration(node) || ts.isTypeAliasDeclaration(node)) &&
        node.getSourceFile() === context.client) {
      return;
    }
    // Another module's code is not its declared types: its function bodies,
    // its decorators and its bindings' initializers run there. A reached
    // declaration's type is its annotation (`annotated`).
    // A part `determining` gives is swept itself, wherever it stands.
    if (!client && !root && (ts.isDecorator(node) || isBody(node) || ts.isClassStaticBlockDeclaration(node) ||
        (node.parent && "initializer" in node.parent && node.parent.initializer === node && !insideType(node.parent))))
      return;
    // Every expression in erased syntax is an entity name or a literal key
    // (`admitted`); any other is refused before a type holding it is
    // replaced, whatever node holds it.
    // A declaration's name is no expression, a private name `#x` included.
    const named = !!node.parent && "name" in node.parent && node.parent.name === node &&
      !ts.isPropertyAccessExpression(node.parent);
    if (!root && ts.isExpression(node) && !named && erased(node, context.client) && !admitted(node))
      throw refusal(node, "an expression in a type or a declared module names a constant (an identifier, a " +
        "property of one read by name) or is a literal: another is erased, and nothing checks what it applies");
    // Every name in erased syntax, each step of a member path included,
    // resolves to the declarations of the symbol it denotes, which are swept.
    // A step a further step selects a member of contributes nothing by
    // itself, only that member; a whole module's type, `typeof import("m")`,
    // contributes its exports.
    if (ts.isIdentifier(node) && !named && erased(node, context.client)) {
      const declarations = context.resolve(node);
      if (!declarations)
        throw refusal(node, "a name in a type or a declared module that TypeScript resolves to no symbol: the " +
          "declarations its meaning depends on are unknown");
      if (!selectedFrom(node)) reach(declarations, node);
    }
    if (ts.isImportTypeNode(node) && !node.qualifier && !selected(node) &&
        ts.isLiteralTypeNode(node.argument) && ts.isStringLiteral(node.argument.literal)) {
      const module = context.moduleOf(node.argument.literal);
      if (!module) throw refusal(node, "an import type naming no module TypeScript resolves");
      reach(module, node);
    }
    // Every form naming a type with arguments: a type reference, simple or
    // qualified (`ns.B<σ>`, `globalThis.Record<K, V>`), an import type
    // (`import("m").B<σ>`), a heritage clause (`extends ns.Base<σ>`); and the
    // forms instantiating a value's generic signature (`typeof f<σ>`,
    // `f<σ>` as an expression), whose binder bounds are checked only at a
    // call and are refused here.
    const form = applicationForm(node);
    if (form?.instantiation) {
      if (form.args.length) {
        const file = node.getSourceFile();
        throw new SweepError(file === context.client ? spanOf(node) : null,
          `the instantiation ${node.getText(file)} in ${site(node)}: a value's type arguments are checked ` +
          "against its binders' bounds only at a call");
      }
      if (form.name) reach(context.declarationsOf(form.name), node);
    } else if (form?.name && !context.declarationsOf(form.name).some(d => env.names.has(d))) {
      application(node, form.name, form.args, env);
    }
    // A member selection's meaning depends on the declarations of the members
    // it selects: an indexed access's at its keys, and a computed alias's,
    // whose equation may select any member of its arguments, at every key.
    if (ts.isIndexedAccessTypeNode(node)) reach(context.members(node.objectType, node.indexType), node);
    if (form?.name && !form.instantiation && context.declarationsOf(form.name).some(d => context.computed(d)))
      for (const arg of form.args) reach(context.members(arg, null), node);
    // Every child is visited, in the scope it is in.
    node.forEachChild(child => { visit(child, scopeOf(node, child, env), client); });
  };
  // The scope a child of `node` is in: a mapped type's key is in scope past
  // its constraint, `infer` binders in the extends type and the true branch,
  // a naked check type narrowed in the true branch, and a declaration's or
  // signature's parameters in all of it.
  const scopeOf = (node: Node, child: Node, env: Env): Env => {
    if (ts.isMappedTypeNode(node)) {
      if (child === node.typeParameter) return env;
      const key = node.typeParameter;
      const names = new Map(env.names);
      names.set(key, fresh(key));
      const level: Binder[] = [{ node: key, name: fresh(key),
        bound: () => key.constraint ? context.read(key.constraint, resolve(env)) : null }];
      return { names, levels: [...env.levels, level] };
    }
    if (ts.isConditionalTypeNode(node)) {
      if (child !== node.extendsType && child !== node.trueType) return env;
      const infers = inferred(node.extendsType);
      const withInfers = infers.length ? group(env, infers) : env;
      return child === node.trueType ? refined(node, withInfers, env) : withInfers;
    }
    const parameters = childParameters(node);
    return parameters.length ? group(env, parameters) : env;
  };
  // The true branch's scope: a naked check type `T` in scope is rebound to
  // a fresh name bounded by `T & X`, X the extends type read in the
  // enclosing scope, as TypeScript narrows `T` there. An extends type with
  // `infer` adds nothing (a weaker scope).
  const refined = (node: ts.ConditionalTypeNode, env: Env, outer: Env): Env => {
    const check = node.checkType;
    if (!ts.isTypeReferenceNode(check) || !ts.isIdentifier(check.typeName) || check.typeArguments?.length ||
        inferred(node.extendsType).length)
      return env;
    // A merged declaration's parameter is one per part: the one in scope.
    const declaration = context.declarationsOf(check.typeName).find(d => outer.names.has(d));
    if (!declaration || !ts.isTypeParameterDeclaration(declaration)) return env;
    const outerName = outer.names.get(declaration);
    if (!outerName) return env;
    const file = node.getSourceFile();
    const name = fresh(declaration, `~${node.getStart(file)}`);
    const names = new Map(env.names);
    names.set(declaration, name);
    const span = spanOf(node);
    const level: Binder[] = [{ node: declaration, name, bound: () => ({ k: "intersection", span,
      parts: [{ k: "binder", name: outerName, span }, context.read(node.extendsType, resolve(outer))] }) }];
    return { names, levels: [...env.levels, level] };
  };
  // The binders an entry keeps: those its arguments name, closed under the
  // binders their bounds name, each with its assumption. Dropping a
  // binder's assumption enlarges the assignments the obligation must hold
  // for, so pruning only strengthens the check.
  const pruned = (env: Env, args: readonly TypeTerm[]): SourceTypeParameter<TypeTerm>[][] => {
    const all = env.levels.flat();
    const kept = new Set<string>();
    const bounds = new Map<string, TypeTerm | null>();
    const mention = (term: TypeTerm): void => visitType(term, t => {
      if (t.k !== "binder" || kept.has(t.name)) return;
      const binder = all.find(b => b.name === t.name);
      if (!binder) return;
      kept.add(t.name);
      const bound = binder.bound();
      bounds.set(t.name, bound);
      if (bound) mention(bound);
    });
    args.forEach(mention);
    return env.levels.map(level => level.filter(b => kept.has(b.name))
      .map(b => ({ name: b.name, bound: bounds.get(b.name) ?? null, resolution: null })))
      .filter(level => level.length);
  };
  const empty: Env = { names: new Map(), levels: [] };
  for (const root of roots) visit(root, empty, root.getSourceFile() === context.client);
  // The binder groups of the declarations enclosing `node`, outermost
  // first.
  const enclosing = (node: Node): Env => {
    const outer: Node[] = [];
    for (let at = node.parent; at; at = at.parent) outer.unshift(at);
    return outer.reduce((env, at) => {
      const parameters = childParameters(at);
      return parameters.length ? group(env, parameters) : env;
    }, empty);
  };
  for (let cursor = 0; cursor < queue.length; cursor++) {
    const node = queue[cursor];
    if (node) visit(node, enclosing(node), false, true);
  }
  return found;
}

/** A form naming a type or a value with type arguments: the name it
 * resolves through (the rightmost of a qualified name; none for a module's
 * namespace), its arguments, and whether it instantiates a value. */
function applicationForm(node: Node): { name: ts.Identifier | null; args: readonly TypeNode[]; instantiation: boolean } | null {
  const rightmost = (name: Node | undefined): ts.Identifier | null =>
    !name ? null : ts.isIdentifier(name) ? name : ts.isQualifiedName(name) ? rightmost(name.right)
      : ts.isPropertyAccessExpression(name) ? rightmost(name.name) : null;
  if (ts.isTypeReferenceNode(node))
    return { name: rightmost(node.typeName), args: node.typeArguments ?? [], instantiation: false };
  if (ts.isImportTypeNode(node))
    return { name: rightmost(node.qualifier), args: node.typeArguments ?? [], instantiation: node.isTypeOf };
  if (ts.isTypeQueryNode(node))
    return { name: rightmost(node.exprName), args: node.typeArguments ?? [], instantiation: true };
  if (ts.isExpressionWithTypeArguments(node))
    return { name: rightmost(node.expression), args: node.typeArguments ?? [],
      instantiation: !(node.parent && ts.isHeritageClause(node.parent)) };
  return null;
}

/** The expressions erased syntax admits: an entity name (an identifier, a
 * property of an entity read by name) and a literal (a string, a number or
 * a bigint, signed or not, `true`, `false`, `null`). Each node is judged by
 * itself; its children are visited and judged in turn. */
function admitted(node: Node): boolean {
  // A heritage clause's entry: its expression is judged in turn.
  if (ts.isExpressionWithTypeArguments(node) && node.parent && ts.isHeritageClause(node.parent)) return true;
  if (ts.isIdentifier(node) || ts.isStringLiteral(node) || ts.isNumericLiteral(node) || ts.isBigIntLiteral(node) ||
      ts.isNoSubstitutionTemplateLiteral(node) || node.kind === ts.SyntaxKind.TrueKeyword ||
      node.kind === ts.SyntaxKind.FalseKeyword || node.kind === ts.SyntaxKind.NullKeyword)
    return true;
  if (ts.isPropertyAccessExpression(node))
    return ts.isIdentifier(node.name) && (ts.isIdentifier(node.expression) || ts.isPropertyAccessExpression(node.expression));
  if (ts.isPrefixUnaryExpression(node))
    return (node.operator === ts.SyntaxKind.MinusToken || node.operator === ts.SyntaxKind.PlusToken) &&
      (ts.isNumericLiteral(node.operand) || ts.isBigIntLiteral(node.operand));
  return false;
}

/** Whether `node` is inside type syntax: a type (a heritage clause's
 * expression excepted, which is code in a class) or an interface. */
function insideType(node: Node): boolean {
  for (let at = node.parent; at; at = at.parent)
    if ((ts.isTypeNode(at) && !ts.isExpressionWithTypeArguments(at)) || ts.isInterfaceDeclaration(at)) return true;
  return false;
}

/** Whether `node` is erased: inside type syntax, or in a module other than
 * the client's, where no code the client runs evaluates it. */
function erased(node: Node, client: ts.SourceFile): boolean {
  return node.getSourceFile() !== client || insideType(node);
}

/** Whether `node` is a function's, method's, accessor's, constructor's or
 * arrow's body, block or expression: code. */
function isBody(node: Node): boolean {
  const owner = node.parent;
  return !!owner && (ts.isFunctionDeclaration(owner) || ts.isFunctionExpression(owner) || ts.isArrowFunction(owner) ||
    ts.isMethodDeclaration(owner) || ts.isGetAccessorDeclaration(owner) || ts.isSetAccessorDeclaration(owner) ||
    ts.isConstructorDeclaration(owner)) && owner.body === node;
}

/** Whether a variable is declared `const`. */
function constant(node: ts.VariableDeclaration): boolean {
  const list = node.parent;
  return !!list && ts.isVariableDeclarationList(list) && (list.flags & ts.NodeFlags.Const) !== 0;
}

/** Whether an expression is a literal naming nothing: a string, number,
 * bigint, Boolean or null, signed or parenthesized, an object or array
 * literal of these, or one of these `as const`. */
function literal(node: Node): boolean {
  if (ts.isStringLiteral(node) || ts.isNumericLiteral(node) || ts.isBigIntLiteral(node) ||
      ts.isNoSubstitutionTemplateLiteral(node) || node.kind === ts.SyntaxKind.TrueKeyword ||
      node.kind === ts.SyntaxKind.FalseKeyword || node.kind === ts.SyntaxKind.NullKeyword)
    return true;
  if (ts.isParenthesizedExpression(node)) return literal(node.expression);
  if (ts.isPrefixUnaryExpression(node))
    return (node.operator === ts.SyntaxKind.MinusToken || node.operator === ts.SyntaxKind.PlusToken) &&
      (ts.isNumericLiteral(node.operand) || ts.isBigIntLiteral(node.operand));
  if (ts.isArrayLiteralExpression(node)) return node.elements.every(literal);
  // `as const` keeps a literal's type syntactic: its literals, readonly.
  if (ts.isAsExpression(node) && ts.isTypeReferenceNode(node.type) && ts.isIdentifier(node.type.typeName) &&
      node.type.typeName.text === "const")
    return literal(node.expression);
  if (ts.isObjectLiteralExpression(node))
    return node.properties.every(p => ts.isPropertyAssignment(p) &&
      (ts.isIdentifier(p.name) || ts.isStringLiteral(p.name) || ts.isNumericLiteral(p.name)) && literal(p.initializer));
  return false;
}

/** Whether a name is a step a further step selects a member of: the left
 * of a qualified name or the object of a property access, or the last name
 * of a `typeof` or an import type an indexed access selects from. */
function selectedFrom(name: Node): boolean {
  let at = name;
  const parent = (n: Node) => n.parent;
  for (let up = parent(at); up && ((ts.isQualifiedName(up) && up.right === at) ||
      (ts.isPropertyAccessExpression(up) && up.name === at)); up = parent(at)) at = up;
  const up = parent(at);
  if (up && ((ts.isQualifiedName(up) && up.left === at) || (ts.isPropertyAccessExpression(up) && up.expression === at)))
    return true;
  return !!up && (ts.isTypeQueryNode(up) || ts.isImportTypeNode(up)) && selected(up);
}

/** Whether a type is the object an indexed access selects from. */
function selected(node: Node): boolean {
  let at = node;
  while (at.parent && ts.isParenthesizedTypeNode(at.parent)) at = at.parent;
  return !!at.parent && ts.isIndexedAccessTypeNode(at.parent) && at.parent.objectType === at;
}

/** The other accessor of the pair `d` belongs to, if any. */
function pairOf(d: ts.GetAccessorDeclaration | ts.SetAccessorDeclaration): Node[] {
  const owner = d.parent;
  const members: readonly Node[] = owner && (ts.isClassDeclaration(owner) || ts.isClassExpression(owner) ||
    ts.isObjectLiteralExpression(owner) || ts.isInterfaceDeclaration(owner) || ts.isTypeLiteralNode(owner))
    ? ts.isObjectLiteralExpression(owner) ? owner.properties : owner.members : [];
  const name = d.name.getText(d.getSourceFile());
  return members.filter(m => m !== d && (ts.isGetAccessorDeclaration(m) || ts.isSetAccessorDeclaration(m)) &&
    m.name.getText(m.getSourceFile()) === name);
}

/** Whether a function's body has overload signatures beside it, the
 * declarations of the same name without a body. */
function overloaded(d: Node): boolean {
  const owner = d.parent;
  const written = (n: Node): string | null => nameOf(n)?.getText(n.getSourceFile()) ?? null;
  const name = written(d);
  const siblings: readonly Node[] = !owner ? [] : ts.isSourceFile(owner) || ts.isModuleBlock(owner) || ts.isBlock(owner)
    ? owner.statements : ts.isClassDeclaration(owner) || ts.isClassExpression(owner) ? owner.members : [];
  return siblings.some(s => s !== d && s.kind === d.kind && !("body" in s && s.body) &&
    (ts.isConstructorDeclaration(d) || written(s) === name));
}

/** Whether `node` is or is in an interface or a type alias. */
function withinTypeDeclaration(node: Node): boolean {
  for (let at: Node | undefined = node; at; at = at.parent)
    if (ts.isInterfaceDeclaration(at) || ts.isTypeAliasDeclaration(at)) return true;
  return false;
}

/** A declaration's or signature's own type parameters. */
function childParameters(node: Node): ts.TypeParameterDeclaration[] {
  const parameters = "typeParameters" in node ? node.typeParameters : undefined;
  return Array.isArray(parameters) ? parameters.filter(ts.isTypeParameterDeclaration) : [];
}

/** The type parameters `infer` declares in `node`. */
function inferred(node: Node): ts.TypeParameterDeclaration[] {
  if (ts.isInferTypeNode(node)) return [node.typeParameter];
  const found: ts.TypeParameterDeclaration[] = [];
  node.forEachChild(child => { found.push(...inferred(child)); });
  return found;
}

function spanOf(node: Node): Span {
  return [node.getStart(node.getSourceFile()), node.end];
}
