/** The typed traversals of the Fragment AST and the declaration document:
 * one map per grammar, of a node's parts, which the folds over a fragment
 * (the names an expression reads, the type terms a fragment holds) and the
 * maps of one (an imported module's identity) use. Each switch is exhaustive
 * over its grammar, so a new kind of node fails to compile until its parts
 * are listed. */
import type { DeclarationDocument, DeclarationIdentity, SourceTypeParameter, TypeTerm, WrittenApplication } from "./declaration-types.mts";
import type { Ast, Expr, FunctionAst, ModuleAst, PatternAst, Stmt, TypeParamAst } from "./fragment.mts";
import { someType } from "./type-term.mts";

/** What a map of a node's parts does to each kind of part: an expression,
 * a statement, a pattern, a type term, a type parameter (its name, bound
 * and resolution slots together). */
export type PartMap = {
  expr: (e: Expr, ...further: unknown[]) => Within<{ value: "any"; store: "grow" }, Expr>;
  stmt: (s: Stmt, ...further: unknown[]) => Within<{ value: "any"; store: "grow" }, Stmt>;
  pattern: (p: PatternAst, ...further: unknown[]) => Within<{ value: "any"; store: "grow" }, PatternAst>;
  type: (t: TypeTerm, ...further: unknown[]) => Within<{ value: "any"; store: "grow" }, TypeTerm>;
  param: (p: TypeParamAst, ...further: unknown[]) => Within<{ value: "any"; store: "grow" }, TypeParamAst>;
};

/** `e` with each of its direct parts mapped by `m`. */
export function mapExprParts(e: Expr, m: PartMap): Within<{ value: "any"; store: "grow" }, Expr> {
  const exprs = (list: Expr[]): Expr[] => list.map(m.expr);
  const types = (list: TypeTerm[]): TypeTerm[] => list.map(m.type);
  switch (e.k) {
    case "id": case "this": case "lit": return e;
    case "not": case "read": case "unary": case "typeofTest": case "arrayTest": return { ...e, e: m.expr(e.e) };
    case "cast": return { ...e, annot: e.annot && m.type(e.annot), e: m.expr(e.e) };
    case "alloc": return { ...e, fields: e.fields.map(f => ({ ...f, e: m.expr(f.e) })),
      ...(e.proto ? { proto: m.expr(e.proto) } : {}) };
    case "build": return { ...e, parts: e.parts.map(p => p.spread !== undefined ? { ...p, spread: m.expr(p.spread) } : { ...p, e: m.expr(p.e) }),
      ...(e.proto ? { proto: m.expr(e.proto) } : {}) };
    case "index": return { ...e, e: m.expr(e.e), key: m.expr(e.key) };
    case "arrayLit": return { ...e, elems: exprs(e.elems) };
    case "arrayAssign": return { ...e,
      targets: e.targets.map(t => ({ ...t, target: m.expr(t.target), default_: t.default_ && m.expr(t.default_) })),
      rest: e.rest && { ...e.rest, target: m.expr(e.rest.target) }, rhs: m.expr(e.rhs) };
    case "indexWrite": return { ...e, receiver: m.expr(e.receiver), key: m.expr(e.key), rhs: m.expr(e.rhs) };
    case "bin": case "arith": return { ...e, l: m.expr(e.l), r: m.expr(e.r) };
    case "update": return { ...e, target: m.expr(e.target), rhs: e.rhs && m.expr(e.rhs) };
    case "coalesce": case "comma": return { ...e, left: m.expr(e.left), right: m.expr(e.right) };
    case "optional": return { ...e, receiver: m.expr(e.receiver), body: m.expr(e.body) };
    case "withObject": return { ...e, object: m.expr(e.object), body: m.expr(e.body) };
    case "tagMember": return { ...e, domain: m.type(e.domain), e: m.expr(e.e) };
    case "write": return { ...e, receiver: m.expr(e.receiver), rhs: m.expr(e.rhs) };
    case "logicalAssign": return { ...e, target: m.expr(e.target), rhs: m.expr(e.rhs) };
    case "nullishAssign": case "assign": return { ...e, rhs: m.expr(e.rhs) };
    case "withValue": return { ...e, fn: m.expr(e.fn), initial: m.expr(e.initial),
      functionType: m.type(e.functionType), bagType: m.type(e.bagType) };
    case "objectAssign": return { ...e, target: m.expr(e.target), sources: exprs(e.sources) };
    case "inTest": return { ...e, key: m.expr(e.key), e: m.expr(e.e) };
    case "instanceTest": return { ...e, e: m.expr(e.e), proto: m.expr(e.proto) };
    case "apply": case "new": case "invoke": return { ...e, callee: m.expr(e.callee), args: exprs(e.args),
      ...(e.typeArgs ? { typeArgs: types(e.typeArgs) } : {}) };
    case "ctor": return { ...e, ...(e.typeParams ? { typeParams: e.typeParams.map(m.param) } : {}),
      lambda: m.expr(e.lambda), ...(e.statics ? { statics: e.statics.map(s => ({ ...s, e: m.expr(s.e) })) } : {}) };
    case "applyWithReceiver": return { ...e, callee: m.expr(e.callee), receiver: m.expr(e.receiver),
      list: e.list && m.expr(e.list) };
    case "callWithReceiver": case "bindWithReceiver": return { ...e, callee: m.expr(e.callee),
      receiver: m.expr(e.receiver), args: exprs(e.args) };
    case "conditional": return { ...e, cond: m.expr(e.cond), then: m.expr(e.then), else_: m.expr(e.else_) };
    case "lambda": return { ...e, typeParams: e.typeParams.map(m.param),
      params: e.params.map(p => ({ ...p, type: m.type(p.type), ...(p.default ? { default: m.expr(p.default) } : {}) })),
      receiver: e.receiver && { ...e.receiver, type: m.type(e.receiver.type) },
      result: e.result && m.type(e.result), guard: e.guard && { ...e.guard, type: m.type(e.guard.type) },
      body: m.expr(e.body) };
    case "blockBody": return { ...e, body: e.body.map(m.stmt) };
    default: { const exhaustive: never = e; return exhaustive; }
  }
}

/** `s` with each of its direct parts mapped by `m`. */
export function mapStmtParts(s: Stmt, m: PartMap): Within<{ value: "any"; store: "grow" }, Stmt> {
  const stmts = (list: Stmt[]): Stmt[] => list.map(m.stmt);
  switch (s.k) {
    case "effect": case "return": case "throw": return { ...s, e: m.expr(s.e) };
    case "break": case "continue": return s;
    case "while": return { ...s, cond: m.expr(s.cond), body: stmts(s.body), update: stmts(s.update) };
    case "block": return { ...s, body: stmts(s.body) };
    case "forOf": return { ...s, iterable: m.expr(s.iterable), body: stmts(s.body) };
    case "closing": return { ...s, close: stmts(s.close), body: stmts(s.body) };
    case "if": return { ...s, cond: m.expr(s.cond), then: stmts(s.then), else_: s.else_ && stmts(s.else_) };
    case "try": return { ...s, body: stmts(s.body), handler: s.handler && { ...s.handler, body: stmts(s.handler.body) },
      finalizer: s.finalizer && stmts(s.finalizer) };
    case "const": case "let": return { ...s,
      bindings: s.bindings.map(b => ({ ...b, annot: b.annot && m.type(b.annot), init: m.expr(b.init) })) };
    case "destructure": return { ...s, target: m.pattern(s.target), default_: s.default_ && m.expr(s.default_),
      init: m.expr(s.init) };
    default: { const exhaustive: never = s; return exhaustive; }
  }
}

/** `p` with each of its direct parts mapped by `m`. */
export function mapPatternParts(p: PatternAst, m: PartMap): Within<{ value: "any"; store: "grow" }, PatternAst> {
  switch (p.k) {
    case "name": return p;
    case "object": return { ...p, props: p.props.map(q => ({ ...q, target: m.pattern(q.target), default_: q.default_ && m.expr(q.default_) })),
      rest: p.rest && { ...p.rest, target: m.pattern(p.rest.target) } };
    case "array": return { ...p, elems: p.elems.map(q => ({ ...q, target: m.pattern(q.target), default_: q.default_ && m.expr(q.default_) })),
      rest: p.rest && { ...p.rest, target: m.pattern(p.rest.target) } };
    default: { const exhaustive: never = p; return exhaustive; }
  }
}

/** `f` with each of its direct parts mapped by `m`. */
export function mapFunctionParts(f: FunctionAst, m: PartMap): Within<{ value: "any"; store: "grow" }, FunctionAst> {
  return { ...f, typeParams: f.typeParams.map(m.param), params: f.params.map(p => ({ ...p, type: m.type(p.type) })),
    retType: m.type(f.retType), guard: f.guard && { ...f.guard, type: m.type(f.guard.type) }, body: f.body.map(m.stmt) };
}

/** The map of every part under a node: its expressions, statements and
 * patterns mapped through their parts, its type terms by `type` and its
 * type parameters by `param`. */
export function deepPartMap(type: (t: TypeTerm, ...further: unknown[]) => Within<{ value: "any"; store: "grow" }, TypeTerm>,
    param: (p: TypeParamAst, ...further: unknown[]) => Within<{ value: "any"; store: "grow" }, TypeParamAst>): Within<{ value: "any"; store: "grow" }, PartMap> {
  function expr(e: Expr): Expr { return mapExprParts(e, deep); }
  function stmt(s: Stmt): Stmt { return mapStmtParts(s, deep); }
  function pattern(p: PatternAst): PatternAst { return mapPatternParts(p, deep); }
  const deep: PartMap = { expr, stmt, pattern, type, param };
  return deep;
}

/** What a map of a declaration document does to each kind of part: a type
 * term, a type parameter, a declaration's identity, a written
 * application's site. */
export type DocumentMap = {
  type: (t: TypeTerm, ...further: unknown[]) => Within<{ value: "any"; store: "grow" }, TypeTerm>;
  param: (p: SourceTypeParameter<TypeTerm>, ...further: unknown[]) => Within<{ value: "any"; store: "grow" }, SourceTypeParameter<TypeTerm>>;
  identity: (id: DeclarationIdentity, ...further: unknown[]) => Within<{ value: "any"; store: "grow" }, DeclarationIdentity>;
  site: (site: string, ...further: unknown[]) => Within<{ value: "any"; store: "grow" }, string>;
};

/** `doc` with each of its parts mapped by `m`. */
export function mapDocument(doc: DeclarationDocument, m: DocumentMap): Within<{ value: "any"; store: "grow" }, DeclarationDocument> {
  const application = (a: WrittenApplication): WrittenApplication => ({ ...a,
    scope: a.scope.map(group => group.map(m.param)),
    reference: { ...a.reference, target: m.identity(a.reference.target) },
    args: a.args.map(m.type), bounds: a.bounds.map(b => b && m.type(b)), site: m.site(a.site) });
  return { ...doc,
    roots: doc.roots.map(r => ({ ...r, declaration: m.identity(r.declaration) })),
    definitions: doc.definitions.map(d => ({ ...d, declaration: m.identity(d.declaration), bases: d.bases.map(m.type),
      expression: d.expression && m.type(d.expression) })),
    values: doc.values.map(v => ({ ...v, declaration: m.identity(v.declaration), typeParams: v.typeParams.map(m.param),
      type: m.type(v.type) })),
    symbols: doc.symbols.map(m.identity),
    applications: doc.applications.map(application) };
}

/** A part of a fragment a fold meets. */
export type Part =
  | { k: "expr"; e: Expr }
  | { k: "stmt"; s: Stmt }
  | { k: "pattern"; p: PatternAst }
  | { k: "type"; t: TypeTerm }
  | { k: "param"; p: TypeParamAst };

/** The direct parts of a node, in the order its map meets them. */
function partsOf(map: (m: PartMap) => unknown): Within<{ value: "any"; store: "grow" }, Part[]> {
  const parts: Part[] = [];
  map({
    expr: e => { parts.push({ k: "expr", e }); return e; },
    stmt: s => { parts.push({ k: "stmt", s }); return s; },
    pattern: p => { parts.push({ k: "pattern", p }); return p; },
    type: t => { parts.push({ k: "type", t }); return t; },
    param: p => { parts.push({ k: "param", p }); return p; },
  });
  return parts;
}

/** A part's direct parts: an expression's, a statement's or a pattern's; a
 * type term and a type parameter are leaves of the fragment's grammar, read
 * by the type terms' own traversal (`typeParts`). */
function directParts(part: Part): Within<{ value: "any"; store: "grow" }, Part[]> {
  switch (part.k) {
    case "expr": return partsOf(m => mapExprParts(part.e, m));
    case "stmt": return partsOf(m => mapStmtParts(part.s, m));
    case "pattern": return partsOf(m => mapPatternParts(part.p, m));
    case "type": case "param": return [];
    default: { const exhaustive: never = part; return exhaustive; }
  }
}

/** Each part under `part`, itself first, depth first. */
export function forEachPart(part: Part, visit: (part: Part) => Within<{ value: "any"; store: "grow" }, void>): Within<{ value: "any"; store: "grow" }, void> {
  visit(part);
  for (const p of directParts(part)) forEachPart(p, visit);
}

/** The type terms a fragment's code states, each a root of its own grammar:
 * annotations, type arguments, a type parameter's bound. */
function fragmentTypes(roots: Part[]): Within<{ value: "any"; store: "grow" }, TypeTerm[]> {
  const types: TypeTerm[] = [];
  for (const root of roots) forEachPart(root, p => {
    if (p.k === "type") types.push(p.t);
    else if (p.k === "param" && p.p.bound) types.push(p.p.bound);
  });
  return types;
}

/** The type terms a declaration document holds, each a root of its own
 * grammar, and the identities it names outside them. */
function documentParts(doc: DeclarationDocument): Within<{ value: "any"; store: "grow" }, { types: TypeTerm[]; identities: DeclarationIdentity[] }> {
  const types: TypeTerm[] = [];
  const identities: DeclarationIdentity[] = [];
  mapDocument(doc, {
    type: t => { types.push(t); return t; },
    param: p => { if (p.bound) types.push(p.bound); return p; },
    identity: id => { identities.push(id); return id; },
    site: site => site,
  });
  return { types, identities };
}

/** Whether a declaration document holds a term passing `term` or names an
 * identity passing `identity`. */
export function documentHolds(doc: DeclarationDocument, term: (t: TypeTerm) => Within<{ value: "any"; store: "grow" }, boolean>,
    identity: (id: DeclarationIdentity, ...further: unknown[]) => Within<{ value: "any"; store: "grow" }, boolean>): Within<{ value: "any"; store: "grow" }, boolean> {
  const declared = documentParts(doc);
  return declared.identities.some(identity) || declared.types.some(t => someType(t, term));
}

/** The parts of a lowered file's code: its top-level statements and its
 * functions'. */
function codeParts(code: { init: Stmt[]; functions: FunctionAst[] }): Within<{ value: "any"; store: "grow" }, Part[]> {
  return [...code.init.map((s): Part => ({ k: "stmt", s })),
    ...code.functions.flatMap(f => partsOf(m => mapFunctionParts(f, m)))];
}

/** Whether a module's documents and code hold a term passing `term` or
 * name an identity passing `identity`. */
export function moduleHolds(module: ModuleAst, term: (t: TypeTerm) => Within<{ value: "any"; store: "grow" }, boolean>,
    identity: (id: DeclarationIdentity, ...further: unknown[]) => Within<{ value: "any"; store: "grow" }, boolean>): Within<{ value: "any"; store: "grow" }, boolean> {
  return documentHolds(module.declarations, term, identity) ||
    fragmentTypes(codeParts(module)).some(t => someType(t, term));
}

/** Whether a file's documents and code, its modules' included, hold a term
 * passing `term` or name an identity passing `identity`. */
export function astHolds(ast: Ast, term: (t: TypeTerm) => Within<{ value: "any"; store: "grow" }, boolean>,
    identity: (id: DeclarationIdentity, ...further: unknown[]) => Within<{ value: "any"; store: "grow" }, boolean>): Within<{ value: "any"; store: "grow" }, boolean> {
  return documentHolds(ast.declarations, term, identity) ||
    fragmentTypes(codeParts(ast)).some(t => someType(t, term)) || ast.modules.some(m => moduleHolds(m, term, identity));
}
