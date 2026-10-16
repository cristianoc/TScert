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
  const reach = (nodes: readonly Node[]): void => {
    for (const node of nodes)
      if (!ts.isSourceFile(node) && !ts.isModuleDeclaration(node) && !context.library(node) && !swept.has(node) &&
          (node.getSourceFile() !== context.client || withinTypeDeclaration(node))) {
        swept.add(node);
        queue.push(node);
      }
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
    reach(target);
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
  const visit = (node: Node, env: Env, client: boolean): void => {
    // A client's interface or alias is swept where something names it.
    if (client && node.parent && (ts.isInterfaceDeclaration(node) || ts.isTypeAliasDeclaration(node)) &&
        node.getSourceFile() === context.client) {
      return;
    }
    // Another module's code is not its declared types: its bodies, its
    // decorators and the initializers of its bindings run there.
    if (!client && (ts.isBlock(node) || ts.isDecorator(node) ||
        (node.parent && "initializer" in node.parent && node.parent.initializer === node && !insideType(node.parent))))
      return;
    // Every expression in erased syntax is an entity name or a literal key
    // (`admitted`); any other is refused before a type holding it is
    // replaced, whatever node holds it.
    // A declaration's name is no expression, a private name `#x` included.
    const named = !!node.parent && "name" in node.parent && node.parent.name === node &&
      !ts.isPropertyAccessExpression(node.parent);
    if (ts.isExpression(node) && !named && erased(node, context.client) && !admitted(node))
      throw refusal(node, "an expression in a type or a declared module names a constant (an identifier, a " +
        "property of one read by name) or is a literal: another is erased, and nothing checks what it applies");
    // Every name in erased syntax, each step of a member path included,
    // resolves to the declarations of the symbol it denotes, which are swept.
    if (ts.isIdentifier(node) && !named && erased(node, context.client)) {
      const declarations = context.resolve(node);
      if (!declarations)
        throw refusal(node, "a name in a type or a declared module that TypeScript resolves to no symbol: the " +
          "declarations its meaning depends on are unknown");
      reach(declarations);
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
      if (form.name) reach(context.declarationsOf(form.name));
    } else if (form?.name && !context.declarationsOf(form.name).some(d => env.names.has(d))) {
      application(node, form.name, form.args, env);
    }
    // A member selection's meaning depends on the declarations of the members
    // it selects: an indexed access's at its keys, and a computed alias's,
    // whose equation may select any member of its arguments, at every key.
    if (ts.isIndexedAccessTypeNode(node)) reach(context.members(node.objectType, node.indexType));
    if (form?.name && !form.instantiation && context.declarationsOf(form.name).some(d => context.computed(d)))
      for (const arg of form.args) reach(context.members(arg, null));
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
    if (node) visit(node, enclosing(node), false);
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
