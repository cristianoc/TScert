/* Part of the trusted front end (fragment-parse.mts): Patterns and statements: destructuring, iteration protocols, loops, `switch`, `try` and declarations.
 * Each exported function is a method of the gate: `Gate` holds it as a field,
 * so a call reads `this.name(...)`; its body names the gate `gate`, typed,
 * which lets a call that never returns (`gate.fail`) narrow what follows. A
 * function that reads nothing of the gate is a module function, called by
 * its binding: a call through a field reads the field's annotation, which
 * states no effect (SOURCE-ELABORATION.md, calls through a location). */
import * as ts from "typescript/unstable/ast";
import type { Expression, FunctionDeclaration, Node, Statement } from "typescript/unstable/ast";
import type { BindingAst, Expr, FunctionAst, FunctionParamAst, Guard, PatternAst, PatternElemAst, PatternPropAst, Stmt } from "./fragment.mts";
import type { Span } from "./span.mts";
import type { IndexFact, StatedEffect, TypeTerm } from "./declaration-types.mts";
import { assertionFailureName, asyncCompleteName, asyncReturnName, forInName, iterateForInName, iterateName } from "./intrinsics.mts";
import { GENERATOR, UNCLOSABLE, booleanForm, booleanReturn, bindingScope, firstOptional, capturesLoopLet, continueBlock, continueLabel, continueTarget, type Loop, forInEntryReads, labeledTarget, statementLabel, freeOffsets, iterationLabel, jumpTarget, nameSlot, namesRead, parameterName, patternNames, skipParentheses, switchLabel, TYPEOF_SHAPES } from "./fragment-support.mts";
import type { Gate } from "./fragment-parse.mts";
import { guardResult } from "./fragment-guards.mts";
import { literalDefaultName } from "./type-term.mts";
import { elaborateRequires, indexFactPositions, requiresTags, type ClauseParameter } from "./bound-annotations.mts";
import { namesView } from "./library-types.mts";
import { aliasMeaning, recordShape } from "./named-record.mts";
import { isImport, isTypeAlias } from "./syntax.mts";

/** The declarator `d` of a pattern, the statement `node` holds it, lowered
 * as a statement of its own at `pos`: the statement's span, or the
 * declarator's where an earlier declarator of its list is lowered before
 * it (`hoisting`). */
export function patternStmt(this: Gate, d: ts.VariableDeclaration, node: Node, mutable: boolean, pos: Span): Within<{ value: "any"; store: "grow" }, Stmt> {
  const gate: Gate = this;
  if (mutable)
    gate.fail(node, "a `let` pattern whose bindings are assigned in a `for` head is outside the fragment: its bindings are cells, which only a statement of a block lowers them to (one never assigned is a `const` pattern)");
  if (!d.initializer) gate.fail(d, "a `const` needs an initializer");
  const kind = gate.iterations.get(gate.span(d.initializer).join(":"));
  if (ts.isArrayBindingPattern(d.name) && kind?.startsWith("client")) {
    if (d.type)
      gate.fail(d, "an annotated array pattern over a program's iterable is outside the fragment: its steps read the iterator, which the annotation does not state");
    if (kind === "client-unclosable" && !d.name.elements.some((e) => ts.isBindingElement(e) && e.dotDotDotToken))
      gate.fail(d.initializer, UNCLOSABLE);
    return gate.protocolPattern(d.name, d.initializer, node, kind === "client-method", pos);
  }
  const target = gate.pattern(d.name, new Set(), ts.isArrayLiteralExpression(skipParentheses(d.initializer)));
  gate.initializedBefore(d, [[target, null]]);
  return {
    k: "destructure",
    pos,
    target,
    default_: null,
    init: gate.patternInit(d, d.initializer),
  };
}

/** The value the declarator `d`, a pattern, destructures, its initializer
 * `init`: under an annotation `T`, `init as T`, the declarator's span: the
 * initializer must meet `T`, which it is typed against, and the pattern
 * reads its parts at `T`. A default under an annotation is refused: the
 * annotation states the type of the binding it replaces `undefined` for,
 * which the default must meet and the lowering states no type for. */
export function patternInit(this: Gate, d: ts.VariableDeclaration, init: Expression): Within<{ value: "any"; store: "grow" }, Expr> {
  const gate: Gate = this;
  if (!d.type) return gate.expr(init);
  const [fallback] = gate.patternDefaults(d.name);
  if (fallback)
    gate.fail(fallback, "a default in an annotated pattern is outside the fragment: the annotation states the binding's type, which the default must meet, and the lowering states no type for one binding of a pattern");
  return { k: "cast", pos: gate.span(d), cast: "as", annot: gate.typeOf(d.type), e: gate.expr(init) };
}

/** `const [a, , b, ...r] = e` over a program's iterable, as ECMA-262's
 * IteratorBindingInitialization runs it: GetIterator, one IteratorStepValue
 * per element until one is done, a hole stepping too; the rest collects
 * every value left; then, the iterator not done (no rest took it to its
 * end), IteratorClose. In ordinary forms, the steps before the source's
 * own declaration, which binds the names from cells no source spells:
 *
 *     let %v0 = undefined, %v2 = undefined;
 *     const %rest = [], %iterator = e[Symbol.iterator](), %next = …;
 *     %done: {
 *       const %result0 = %next(); if (%result0.done) break %done; %v0 = %result0.value;
 *       …
 *       while (true) { const %resultR = %next(); if (%resultR.done) break %done; %rest.push(%resultR.value); }
 *       // or, without a rest, the close of `protocolForOf`
 *     }
 *     const a = %v0, b = %v2, r = %rest;
 *
 * Binding a name runs nothing, so binding each after the steps is binding
 * it at its step. A default or a nested pattern, which run code between
 * the steps (and IteratorClose on a throw of theirs), is outside it. */
export function protocolPattern(this: Gate, pattern: ts.ArrayBindingPattern, init: Expression, node: Node, method: boolean, pos: Span): Within<{ value: "any"; store: "grow" }, Stmt> {
  const gate: Gate = this;
  if (gate.hoist?.stmt !== node)
    gate.fail(node, "an array pattern over a program's iterable is outside the fragment here: its steps are statements, with cells, before the declaration, which a function's or a closure's body has and a module's top level or a `for` initializer does not");
  const site = gate.hoist.site;
  const tag = `${pattern.getStart(gate.file)}`;
  const label = `%done@${tag}`;
  const elements = pattern.elements;
  const rest = elements.at(-1);
  const restName = rest && ts.isBindingElement(rest) && rest.dotDotDotToken ? rest : null;
  const named: { cell: string; name: ts.Identifier }[] = [];
  elements.forEach((el, i) => {
    if (!ts.isBindingElement(el) || !el.name || el === restName) return;
    if (el.initializer || !el.name || !ts.isIdentifier(el.name) || el.dotDotDotToken)
      gate.fail(el, "a default or a nested pattern in an array pattern over a program's iterable is outside the fragment: it runs code between the iterator's steps, which the lowering does not interleave");
    if (el.name.text === "undefined") gate.fail(el, "shadowing undefined is outside the fragment");
    named.push({ cell: `%v${i}@${tag}`, name: el.name });
  });
  if (restName && (!restName.name || !ts.isIdentifier(restName.name)))
    gate.fail(restName, "a nested pattern in an array pattern's rest over a program's iterable is outside the fragment");
  const restCell = `%rest@${tag}`;
  const statements: Stmt[] = [];
  if (named.length) {
    const e = site.entry();
    const cells: BindingAst[] = [];
    for (const { cell } of named) {
      const at = site.span();
      cells.push({ early: false, name: cell, namePos: at, annot: null, init: { k: "lit", pos: at, lit: { a: "undefined" } } });
    }
    statements.push({ k: "let", pos: [e, e + 1], bindings: cells });
  }
  const start = gate.protocolStart(gate.expr(init), site, tag, init);
  const e0 = site.entry();
  const restAt = site.span();
  const restBinding: BindingAst[] = restName
    ? [{ early: false, name: restCell, namePos: restAt, annot: null, init: { k: "arrayLit", pos: restAt, elems: [] } }] : [];
  statements.push({ k: "const", pos: [e0, e0 + 1], bindings: [...restBinding, ...start.bindings] });
  const leave = (): Stmt => {
    const e = site.entry();
    return { k: "break", pos: [e, e + 1], label };
  };
  const inner: Stmt[] = [];
  elements.forEach((el, i) => {
    if (el === restName) return;
    const step = gate.protocolStep(start.next, `%result${i}@${tag}`, leave, site);
    inner.push(...step.stmts);
    const cell = named.find((n) => n.cell === `%v${i}@${tag}`);
    if (cell) {
      const e = site.entry();
      const at = site.span();
      inner.push({ k: "effect", pos: [e, e + 1],
        e: { k: "assign", pos: at, name: cell.cell, namePos: site.span(), rhs: step.value() } });
    }
  });
  if (restName) {
    const eLoop = site.entry();
    inner.push({ k: "while", pos: [eLoop, eLoop + 1], update: [],
      cond: { k: "lit", pos: site.span(), lit: { a: "booleanlit", v: "true" } },
      body: gate.collectStep(start.next, `%resultRest@${tag}`, restCell, leave, site) });
  } else inner.push(...this.closeStatements(start.iteratorAt, tag, site, method));
  statements.push({ k: "block", pos, label, body: inner });
  gate.hoisted.push(...statements);
  const bindings: BindingAst[] = [];
  for (const { cell, name } of named)
    bindings.push({ early: false, name: gate.local(name), namePos: gate.span(name), annot: null,
      init: { k: "id", pos: gate.span(name), name: cell } });
  if (restName && restName.name && ts.isIdentifier(restName.name))
    bindings.push({ early: false, name: gate.local(restName.name), namePos: gate.span(restName.name), annot: null,
      init: { k: "id", pos: gate.span(restName.name), name: restCell } });
  return { k: "const", pos, bindings };
}

/** One step of a collecting loop: the step, its `done` leaving by `leave`,
 * and the value pushed onto the fresh array `items`. */
export function collectStep(this: Gate, next: string, result: string, items: string, leave: () => Within<{ value: "any"; store: "grow" }, Stmt>,
    site: { entry(): Within<{ value: "any"; store: "grow" }, number>; span(): Within<{ value: "any"; store: "grow" }, Span> }): Within<{ value: "any"; store: "grow" }, Stmt[]> {
  const gate: Gate = this;
  const step = gate.protocolStep(next, result, leave, site);
  const e = site.entry();
  const pushAt = site.span(), pushRead = site.span(), itemsAt = site.span();
  return [...step.stmts, { k: "effect", pos: [e, e + 1], e: { k: "invoke", pos: pushAt, args: [step.value()],
    callee: { k: "read", pos: pushRead, field: "push", e: { k: "id", pos: itemsAt, name: items } } } }];
}

/** IteratorClose where nothing is thrown: the iterator's `return`, read
 * once, called on it where it is not `undefined`, its result an object
 * (`protocolForOf`). A `return` the iterator's type declares a required
 * method (`method`) is a method member, read bound to the iterator
 * (`o.m.bind(o)`, which reads it once) and always present. */
export function closeStatements(this: Gate, iteratorAt: () => Within<{ value: "any"; store: "grow" }, Expr>, tag: string, site: { entry(): Within<{ value: "any"; store: "grow" }, number>; span(): Within<{ value: "any"; store: "grow" }, Span> },
    method: boolean): Within<{ value: "any"; store: "grow" }, Stmt[]> {
  const member = `%return@${tag}`, closed = `%closed@${tag}`;
  const e1 = site.entry();
  if (method) {
    const e2 = site.entry();
    const boundAt = site.span(), readAt = site.span(), callAt = site.span(), memberAt = site.span(),
      objectAt = site.span();
    return [
      { k: "const", pos: [e1, e1 + 1], bindings: [{ early: false, name: member, namePos: boundAt, annot: null,
        init: { k: "bindWithReceiver", pos: boundAt, args: [],
          callee: { k: "read", pos: readAt, field: "return", e: iteratorAt() }, receiver: iteratorAt() } }] },
      { k: "const", pos: [e2, e2 + 1], bindings: [{ early: false, name: closed, namePos: callAt,
        annot: { k: "atom", name: "object", span: objectAt },
        init: { k: "apply", pos: callAt, callee: { k: "id", pos: memberAt, name: member }, args: [] } }] },
    ];
  }
  const e2 = site.entry(), e3 = site.entry();
  const readAt = site.span(), testAt = site.span(), narrowed = site.span(), callAt = site.span(),
    objectAt = site.span();
  return [
    { k: "const", pos: [e1, e1 + 1], bindings: [{ early: false, name: member, namePos: readAt, annot: null,
      init: { k: "read", pos: readAt, field: "return", e: iteratorAt() } }] },
    { k: "if", pos: [e2, e2 + 1],
      // The member's read and the name holding it are one value, at one
      // claim site.
      cond: { k: "typeofTest", pos: testAt, shape: "undefined", equal: false,
        e: { k: "id", pos: readAt, name: member } },
      then: [{ k: "const", pos: [e3, e3 + 1], bindings: [{ early: false, name: closed, namePos: callAt,
        annot: { k: "atom", name: "object", span: objectAt },
        init: { k: "callWithReceiver", pos: callAt, callee: { k: "id", pos: narrowed, name: member },
          receiver: iteratorAt(), args: [] } }] }],
      else_: null },
  ];
}

/** A spread of a program's iterable, `...e`, collected into a fresh array
 * before the statement it is in (`hoist`): the steps of `protocolForOf`,
 * closing nothing (a spread steps until done), each value pushed onto the
 * array, which the spread then stands for. */
export function collect(this: Gate, operand: Expression): Within<{ value: "any"; store: "grow" }, Expr> {
  const gate: Gate = this;
  const hoist = gate.hoist;
  if (!hoist) throw Error("internal: a spread collected outside its statement");
  const site = hoist.site;
  const tag = `${operand.getStart(gate.file)}`;
  const items = `%items@${tag}`;
  const start = gate.protocolStart(gate.expr(operand), site, tag, operand);
  const e0 = site.entry();
  const itemsAt = site.span();
  const eLoop = site.entry();
  const leave = (): Stmt => {
    const e = site.entry();
    return { k: "break", pos: [e, e + 1], label: null };
  };
  gate.hoisted.push(
    { k: "const", pos: [e0, e0 + 1], bindings: [
      { early: false, name: items, namePos: itemsAt, annot: null, init: { k: "arrayLit", pos: itemsAt, elems: [] } },
      ...start.bindings] },
    { k: "while", pos: [eLoop, eLoop + 1], update: [],
      cond: { k: "lit", pos: site.span(), lit: { a: "booleanlit", v: "true" } },
      body: gate.collectStep(start.next, `%result@${tag}`, items, leave, site) });
  return { k: "id", pos: site.span(), name: items };
}

/** The spread of a program's iterable the statement `s` runs, where the
 * collection may run before the statement: the first evaluation of the
 * statement's value that may run code, every evaluation before it a name or
 * a literal, none of the names assigned anywhere in the file, so that what
 * they hold before the iterator's code runs is what they hold after. The
 * value is an expression statement's, a `return`'s or a declaration's one
 * initializer, and evaluation is followed in JavaScript's order: an array
 * literal's elements, a call's or construction's callee then arguments, a
 * member read's object. */
export function hoistTarget(this: Gate, s: Statement): Within<{ value: "any"; store: "grow" }, ts.SpreadElement | null> {
  const gate: Gate = this;
  let e: Expression | undefined;
  if (ts.isExpressionStatement(s)) e = s.expression;
  else if (ts.isReturnStatement(s)) e = s.expression;
  else if (ts.isVariableStatement(s)) {
    const [only, ...others] = s.declarationList.declarations;
    if (only && !others.length && ts.isIdentifier(only.name)) e = only.initializer;
  }
  if (!e) return null;
  const program = (x: Node) => {
    const kind = gate.iterations.get(gate.span(x).join(":"));
    return !!kind?.startsWith("client");
  };
  // A name read before the spread runs after the collection: it must hold
  // the same value then, and its read must not throw where the source's
  // would (`unassigned`).
  const stable = (x: Node) => ts.isIdentifier(x) ? gate.unassigned(x)
    : ts.isNumericLiteral(x) || ts.isStringLiteral(x) || x.kind === ts.SyntaxKind.TrueKeyword ||
      x.kind === ts.SyntaxKind.FalseKeyword || x.kind === ts.SyntaxKind.NullKeyword;
  // The spread, if it is the first evaluation of `x` that may run code;
  // `"stable"` where `x` runs none; null where code runs before it.
  const first = (x: Node): ts.SpreadElement | "stable" | null => {
    while (ts.isParenthesizedExpression(x)) x = x.expression;
    if (stable(x)) return "stable";
    const sequence = (parts: readonly Node[]): ts.SpreadElement | "stable" | null => {
      for (const part of parts) {
        if (ts.isSpreadElement(part) && program(part.expression)) return part;
        if (!stable(part)) {
          const inner = first(part);
          return inner === "stable" ? null : inner;
        }
      }
      return "stable";
    };
    if (ts.isArrayLiteralExpression(x)) return sequence(x.elements) === "stable" ? null : sequence(x.elements);
    if ((ts.isCallExpression(x) && !x.questionDotToken) || ts.isNewExpression(x)) {
      // A callee that is a stable name is read where the call is; a method
      // read off a value reads that value's member, which the iterator's
      // code may change, so the spread must come first within the value.
      const callee = x.expression;
      if (stable(callee)) {
        const found = sequence(x.arguments ?? []);
        return found === "stable" ? null : found;
      }
      const head = ts.isPropertyAccessExpression(callee) && !callee.questionDotToken ? callee.expression : callee;
      const inner = first(head);
      return inner === "stable" ? null : inner;
    }
    if (ts.isPropertyAccessExpression(x) && !x.questionDotToken) {
      const inner = first(x.expression);
      return inner === "stable" ? null : inner;
    }
    return null;
  };
  const found = first(e);
  return found === "stable" ? null : found;
}

/** The scope of the binding a read of the name `id` reads, where the read
 * cannot throw nor run code, and gives the value it gives at any other read
 * where nothing writes the binding (`unassigned`); null where it may throw.
 * The walk out from `id` stops at the first binding of its name: a parameter
 * read after its own declaration, a function declaration with a body, a
 * block's or a `switch` clause's `let` or `const` (of a pattern too) the
 * early-binding analysis finds initialized at every read (`markEarly`), a
 * loop's `let` or `const` binding read in the loop's body (or a `for`
 * loop's test or update), a `catch` clause's binding read in its block; past
 * every binding, a name TypeScript binds to the standard library's `var`s or
 * functions alone (`libraryValues`), whose scope here is the file. A module binding, an import, a class,
 * an enum, a namespace, a named function or class expression's own name, a
 * binding of another `switch` clause, an ambient or unresolved name is not
 * one. */
export function readScope(this: Gate, id: ts.Identifier): Within<{ value: "any"; store: "grow" }, Node | null> {
  const gate: Gate = this;
  for (let at: Node | undefined = id.parent; at; at = at.parent) {
    // A parameter is bound before the body runs and before the later
    // parameters' defaults; read in its own, or in an earlier one's, it is
    // uninitialized.
    const parameter = functionLikeNode(at) ? at.parameters.find(p => bindsName(p.name, id.text)) : undefined;
    if (parameter) return id.pos >= parameter.end ? at : null;
    // A loop's `let` or `const` binding is bound before its body runs, and
    // before a `for` loop's test and update; a `catch` clause's before its
    // block. Read in the head declaring it, it is uninitialized; a `var`
    // there holds `undefined` until its initializer runs.
    const loop = ts.isForOfStatement(at) || ts.isForInStatement(at) || ts.isForStatement(at) ? at : undefined;
    const loopHead = loop?.initializer;
    if (loop && loopHead && ts.isVariableDeclarationList(loopHead) &&
        loopHead.declarations.some(d => bindsName(d.name, id.text)))
      return !!(loopHead.flags & (ts.NodeFlags.Let | ts.NodeFlags.Const)) &&
        [loop.statement, ...(ts.isForStatement(loop) ? [loop.condition, loop.incrementor] : [])]
          .some(region => !!region && within(id, region)) ? loop : null;
    if (ts.isCatchClause(at) && at.variableDeclaration && bindsName(at.variableDeclaration.name, id.text))
      return within(id, at.block) ? at : null;
    // A named function or class expression binds its name within itself:
    // the walk stops there, at a binding read through no slot of the
    // Fragment's.
    if ((ts.isFunctionExpression(at) || ts.isClassExpression(at)) && at.name?.text === id.text) return null;
    // A `switch`'s clauses share one scope: a binding of one clause read
    // in another may be uninitialized.
    const clauses = ts.isCaseBlock(at) ? at.clauses : null;
    const statements: readonly Statement[] | null = ts.isBlock(at) || ts.isSourceFile(at) ? at.statements
      : clauses ? clauses.flatMap((c): Statement[] => [...c.statements]) : null;
    if (!statements) continue;
    for (const st of statements) {
      // A function declaration with a body is created when its scope is
      // entered; an ambient one (`declare function`, an overload without
      // a body) says nothing of what the name holds at run time.
      if (ts.isFunctionDeclaration(st) && st.name?.text === id.text) {
        const named = statements.filter((d): d is ts.FunctionDeclaration =>
          ts.isFunctionDeclaration(d) && d.name?.text === id.text);
        return named.some(d => !!d.body) &&
          !named.some(d => d.modifiers?.some(m => m.kind === ts.SyntaxKind.DeclareKeyword)) ? at : null;
      }
      if ((ts.isClassDeclaration(st) || ts.isEnumDeclaration(st) || ts.isModuleDeclaration(st)) &&
          st.name && ts.isIdentifier(st.name) && st.name.text === id.text) return null;
      if (isImport(st) && importedNames(st).includes(id.text)) return null;
      if (ts.isVariableStatement(st))
        for (const d of st.declarationList.declarations)
          if (bindsName(d.name, id.text)) {
            if (ts.isSourceFile(at) || !(st.declarationList.flags & (ts.NodeFlags.Let | ts.NodeFlags.Const)) ||
                (clauses && !clauses.some(c => within(st, c) && within(id, c))))
              return null;
            // A pattern's binding read where it may be uninitialized is
            // refused by the early-binding analysis (`markEarly`).
            return !ts.isIdentifier(d.name) || !gate.earlyDecls.has(d) ? at : null;
          }
    }
  }
  return gate.libraryValues.has(gate.span(id).join(":")) ? gate.file : null;
}

/** Whether every read of the name `id` gives one value: its read cannot
 * throw nor run code (`readScope`), and no write in its binding's scope names
 * the binding (`writesName`), a nested closure's included. Code outside that
 * scope cannot name the binding. */
export function unassigned(this: Gate, id: ts.Identifier): Within<{ value: "any"; store: "grow" }, boolean> {
  const gate: Gate = this;
  const scope = gate.readScope(id);
  return scope !== null && !writesName(gate, scope, new Set([gate.local(id)]));
}

/** Whether a binding name, an identifier or a pattern, binds `name`. */
const bindsName = (b: ts.BindingName, name: string): Within<{ value: "any"; store: "grow" }, boolean> =>
  ts.isIdentifier(b) ? b.text === name
    : b.elements.some(e => !ts.isOmittedExpression(e) && !!e.name && bindsName(e.name, name));

/** Whether `n` lies within `region`. */
const within = (n: Node, region: Node): Within<{ value: "any"; store: "grow" }, boolean> => n.pos >= region.pos && n.end <= region.end;

/** The local names an import declaration binds. */
const importedNames = (st: ts.ImportDeclaration): Within<{ value: "any"; store: "grow" }, string[]> => {
  const clause = st.importClause;
  if (!clause) return [];
  const bindings = clause.namedBindings;
  return [...(clause.name ? [clause.name.text] : []),
    ...(bindings && ts.isNamespaceImport(bindings) ? [bindings.name.text] : []),
    ...(bindings && ts.isNamedImports(bindings) ? bindings.elements.map(e => e.name.text) : [])];
};

const functionLikeNode = (n: Node): n is ts.FunctionDeclaration | ts.FunctionExpression | ts.ArrowFunction |
    ts.MethodDeclaration | ts.ConstructorDeclaration =>
  ts.isFunctionDeclaration(n) || ts.isFunctionExpression(n) || ts.isArrowFunction(n) || ts.isMethodDeclaration(n) ||
  ts.isConstructorDeclaration(n);

export function initializedBefore(this: Gate, at: Node, targets: [PatternAst, Expr | null][]): Within<{ value: "any"; store: "grow" }, void> {
  const gate: Gate = this;
  const own = new Set(targets.flatMap(([t]) => patternNames(t)));
  const bound = new Set<string>();
  const check = (d: Expr | null): void => {
    if (d && [...namesRead(d)].some((n) => own.has(n) && !bound.has(n)))
      gate.fail(at, "a default reads a binding of its own declaration before it is initialized");
  };
  const visit = (t: PatternAst, d: Expr | null): void => {
    check(d);
    if (t.k === "name") bound.add(t.name);
    else if (t.k === "object") {
      for (const q of t.props) visit(q.target, q.default_);
      if (t.rest) visit(t.rest.target, null);
    }
    else {
      for (const q of t.elems) visit(q.target, q.default_);
      if (t.rest) visit(t.rest.target, null);
    }
  };
  for (const [t, d] of targets) visit(t, d);
}

export function inert(this: Gate, e: Node): Within<{ value: "keep"; store: "keep" }, boolean> {
  const gate: Gate = this;
  if (ts.isNumericLiteral(e) || ts.isBigIntLiteral(e) || ts.isStringLiteral(e) ||
      ts.isNoSubstitutionTemplateLiteral(e) || ts.isIdentifier(e) || ts.isArrowFunction(e) ||
      ts.isFunctionExpression(e) || ts.isOmittedExpression(e))
    return true;
  switch (e.kind) {
    case ts.SyntaxKind.TrueKeyword: case ts.SyntaxKind.FalseKeyword:
    case ts.SyntaxKind.NullKeyword: case ts.SyntaxKind.ThisKeyword:
      return true;
  }
  if (ts.isParenthesizedExpression(e) || ts.isAsExpression(e) || ts.isSatisfiesExpression(e) ||
      ts.isNonNullExpression(e) || ts.isPropertyAccessExpression(e) || ts.isTypeOfExpression(e) ||
      ts.isVoidExpression(e))
    return gate.inert(e.expression);
  if (ts.isElementAccessExpression(e))
    return gate.inert(e.expression) && (ts.isStringLiteral(e.argumentExpression) ||
      ts.isNumericLiteral(e.argumentExpression));
  if (ts.isPrefixUnaryExpression(e))
    return e.operator === ts.SyntaxKind.ExclamationToken ? gate.inert(e.operand)
      : (e.operator === ts.SyntaxKind.MinusToken || e.operator === ts.SyntaxKind.PlusToken) &&
        (ts.isNumericLiteral(e.operand) || ts.isBigIntLiteral(e.operand));
  if (ts.isConditionalExpression(e))
    return gate.inert(e.condition) && gate.inert(e.whenTrue) && gate.inert(e.whenFalse);
  if (ts.isBinaryExpression(e)) {
    const op = e.operatorToken.kind;
    if (op === ts.SyntaxKind.EqualsToken) return ts.isIdentifier(e.left) && gate.inert(e.right);
    return (op === ts.SyntaxKind.EqualsEqualsEqualsToken || op === ts.SyntaxKind.ExclamationEqualsEqualsToken ||
      op === ts.SyntaxKind.AmpersandAmpersandToken || op === ts.SyntaxKind.BarBarToken ||
      op === ts.SyntaxKind.QuestionQuestionToken || op === ts.SyntaxKind.CommaToken) &&
      gate.inert(e.left) && gate.inert(e.right);
  }
  if (ts.isArrayLiteralExpression(e)) return e.elements.every((x) => !ts.isSpreadElement(x) && gate.inert(x));
  if (ts.isObjectLiteralExpression(e))
    return e.properties.every((p) => ts.isShorthandPropertyAssignment(p) && !p.objectAssignmentInitializer ||
      ts.isPropertyAssignment(p) && !ts.isComputedPropertyName(p.name) && gate.inert(p.initializer));
  return false;
}

export function patternDefaults(this: Gate, node: ts.BindingName): Within<{ value: "keep"; store: "keep" }, Node[]> {
  const gate: Gate = this;
  if (ts.isIdentifier(node)) return [];
  return node.elements.flatMap((el): Node[] => ts.isOmittedExpression(el) ? []
    : [...(el.initializer ? [el.initializer] : []), ...(el.name ? gate.patternDefaults(el.name) : [])]);
}

export function steppedPattern(this: Gate, fresh: boolean,
    elements: { node: Node; hole: boolean; before: Node[]; after: Node[] }[]): Within<{ value: "any"; store: "keep" }, void> {
  const gate: Gate = this;
  if (fresh) return;
  let last = -1;
  elements.forEach((el, i) => { if (!el.hole) last = i; });
  const refuse = (node: Node, what: string): never => gate.fail(node,
    `an array pattern over an array another reference may hold, with ${what} after one of its steps and before a later one, is outside the fragment: JavaScript steps the array's iterator, which stays finished once a step found the end, while the lowering reads each position, which sees what such code added to the array`);
  elements.forEach((el, i) => {
    if (i > 0 && i <= last)
      for (const n of el.before) if (!gate.inert(n)) refuse(n, "a target's reference that may call or write");
    if (i < last)
      for (const n of el.after)
        if (ts.isPropertyAccessExpression(n) || ts.isElementAccessExpression(n)) refuse(n, "a write at a field target's index or length");
        else if (!gate.inert(n)) refuse(n, "a default that may call or write");
  });
}

export function assignedSteps(this: Gate, left: ts.ArrayLiteralExpression):
    Within<{ value: "any"; store: "grow" }, { node: Node; hole: boolean; before: Node[]; after: Node[] }[]> {
  return left.elements.map((el) => {
    if (ts.isOmittedExpression(el)) return { node: el, hole: true, before: [], after: [] };
    const assigned = ts.isBinaryExpression(el) && el.operatorToken.kind === ts.SyntaxKind.EqualsToken ? el : null;
    const target = ts.isSpreadElement(el) ? el.expression : assigned ? assigned.left : el;
    const before: Node[] = ts.isPropertyAccessExpression(target) ? [target.expression]
      : ts.isElementAccessExpression(target) ? [target.expression, target.argumentExpression] : [];
    const write: Node[] = ts.isElementAccessExpression(target) ||
      ts.isPropertyAccessExpression(target) && ts.isIdentifier(target.name) && target.name.text === "length"
      ? [target] : [];
    return { node: el, hole: false, before, after: [...(assigned ? [assigned.right] : []), ...write] };
  });
}

export function pattern(this: Gate, node: ts.BindingName, names: Set<string>, fresh: boolean = false): Within<{ value: "any"; store: "grow" }, PatternAst> {
  const gate: Gate = this;
  if (ts.isIdentifier(node)) {
    if (node.text === "undefined")
      gate.fail(node, "shadowing undefined is outside the fragment");
    if (names.has(node.text)) gate.fail(node, "duplicate pattern binding");
    names.add(node.text);
    return { k: "name", name: gate.local(node), pos: gate.span(node) };
  }
  if (node.elements.length === 0)
    gate.fail(node, "an empty pattern binds nothing");
  if (ts.isArrayBindingPattern(node)) {
    gate.steppedPattern(fresh, node.elements.map((el) => ts.isOmittedExpression(el) || !el.name
      ? { node: el, hole: true, before: [], after: [] }
      : { node: el, hole: false, before: [],
          after: [...(el.initializer ? [el.initializer] : []), ...this.patternDefaults(el.name)] }));
    const elems: PatternElemAst[] = [];
    let rest: Extract<PatternAst, { k: "array" }>["rest"] = null;
    node.elements.forEach((el, index) => {
      // A hole is an omitted expression, or a binding element without a name.
      if (ts.isOmittedExpression(el) || !el.name) return;
      if (el.dotDotDotToken)
        rest = { index, pos: gate.span(el), target: gate.pattern(el.name, names),
          slice: gate.slices.has(gate.span(node).join(":")) };
      else
        elems.push({
          index,
          target: gate.pattern(el.name, names),
          default_: el.initializer ? gate.expr(el.initializer) : null,
        });
    });
    return { k: "array", pos: gate.span(node), elems, rest };
  }
  // An object rest, last, copies the source's other own enumerable
  // properties onto a fresh object (SOURCE-MODEL.md, "Object literals").
  let rest: Extract<PatternAst, { k: "object" }>["rest"] = null;
  const last = node.elements[node.elements.length - 1];
  if (last?.dotDotDotToken) {
    const restName = last.name;
    if (!restName || !ts.isIdentifier(restName)) return gate.fail(last, "an object rest binds a name");
    rest = { pos: gate.span(last), target: gate.pattern(restName, names) };
  }
  const props: PatternPropAst[] = node.elements.filter((el) => !el.dotDotDotToken).map((el) => {
    if (!el.name) gate.fail(el, "a pattern element needs a name");
    const key = el.propertyName ?? el.name;
    if (!ts.isIdentifier(key))
      gate.fail(el, "computed or string pattern keys are outside the fragment");
    return {
      field: key.text,
      target: gate.pattern(el.name, names),
      default_: el.initializer ? gate.expr(el.initializer) : null,
    };
  });
  return { k: "object", pos: gate.span(node), props, rest };
}

export function block(this: Gate, node: Statement): Within<{ value: "any"; store: "grow" }, Stmt[]> {
  const gate: Gate = this;
  if (!ts.isBlock(node)) {
    if (ts.isVariableStatement(node))
      gate.fail(node, "a declaration requires a block body");
    return gate.statements([node]);
  }
  return gate.statements(node.statements);
}

/** A statement list, without its dead tail: the statements after one that
 * always completes abruptly (`abrupt`) are never reached, since nothing can
 * jump into the middle of a list. They are dropped unread when dropping them
 * changes no binding the live statements see: a `var` there is hoisted, and
 * a `let`, `const` or `class` there binds its name in the whole block, so a
 * live reference to it would be to that binding, forever uninitialized. A
 * function declaration of the list there is bound at the block's entry, as
 * one before it is (`functionPlacement`). */
export function statements(this: Gate, list: readonly Statement[]): Within<{ value: "any"; store: "grow" }, Stmt[]> {
  const gate: Gate = this;
  const end = list.findIndex((s) => abrupt(s));
  const live = end < 0 ? list : list.slice(0, end + 1);
  const lexical = new Set<string>();
  const hoisted = (n: Node): Node | undefined => {
    if (ts.isFunctionDeclaration(n) ||
        (ts.isVariableDeclarationList(n) && !(n.flags & (ts.NodeFlags.Let | ts.NodeFlags.Const))))
      return n;
    if (ts.isFunctionLikeDeclaration(n) || ts.isClassLikeDeclaration(n)) return undefined;
    return n.forEachChild(hoisted);
  };
  const names = (n: Node): void => {
    if (ts.isIdentifier(n)) lexical.add(n.text);
    else n.forEachChild(names);
  };
  const tail = list.slice(live.length).filter((s): s is FunctionDeclaration => ts.isFunctionDeclaration(s));
  for (const s of list.slice(live.length)) {
    if (typeStatement(s) || ts.isFunctionDeclaration(s)) continue;
    const at = hoisted(s);
    if (at) gate.fail(at, "a hoisted declaration after a statement that always jumps is outside the fragment");
    if (ts.isVariableStatement(s))
      for (const d of s.declarationList.declarations) names(d.name);
    else if (ts.isClassDeclaration(s) && s.name) lexical.add(s.name.text);
    else if (ts.SyntaxKind[s.kind].endsWith("Declaration"))
      gate.fail(s, "a declaration after a statement that always jumps is outside the fragment");
  }
  const refers = (n: Node): Node | undefined =>
    ts.isIdentifier(n) && lexical.has(n.text) ? n : n.forEachChild(refers);
  // The list's statements that may run: the live ones and the function
  // declarations of the tail.
  const scope = [...live, ...tail];
  for (const s of scope) {
    const at = lexical.size ? refers(s) : undefined;
    if (at) gate.fail(at, "a name declared only in dead code is outside the fragment");
  }
  const placed = functionPlacement(gate, scope);
  gate.markEarly(scope, placed);
  // A function declaration is a constant holding its closure, bound before
  // the statement `functionPlacement` places it at (`functionDeclarations`);
  // one placed in the tail is never read, and never bound.
  const functions = gate.functionDeclarations(scope, live.length, placed);
  // An empty statement, `;`, does nothing; nor does a type declaration.
  return live.flatMap((s, i) => [...(functions.get(i) ?? []),
    ...(ts.isEmptyStatement(s) || typeStatement(s) || ts.isFunctionDeclaration(s) ? [] : gate.hoisting(s))]);
}

/** Where each function declaration of a statement list is bound: before
 * the list's statement of that index. JavaScript creates a function
 * declaration's closure, and initializes its binding, when the list's
 * block is entered. Creating a closure runs nothing, and the new object is
 * reached only through its binding, so creating it later, before the first
 * statement that may read the binding, is the same execution: its place is
 * the first statement of the list mentioning it, or holding a closure that
 * does, or the place of another function declaration mentioning it,
 * whichever comes first, and at most its own. A mention of a declaration
 * is the identifier the fragment names it by (`local`), outside types and
 * property keys. */
export function functionPlacement(gate: Gate, live: readonly Statement[]): Within<{ value: "any"; store: "grow" }, Map<FunctionDeclaration, number>> {
  const placed = new Map<FunctionDeclaration, number>();
  const byName = new Map<string, FunctionDeclaration>();
  live.forEach((s, i) => {
    if (!ts.isFunctionDeclaration(s) || !s.name) return;
    placed.set(s, i);
    byName.set(gate.local(s.name), s);
  });
  if (!placed.size) return placed;
  const mentioned = (n: Node, own: Node | null, found: Set<FunctionDeclaration>): void => {
    if (ts.isTypeNode(n)) return;
    if (ts.isIdentifier(n)) {
      const parent = n.parent;
      const key = !!parent && (((ts.isPropertyAccessExpression(parent) && parent.name === n) ||
        ((ts.isPropertyAssignment(parent) || ts.isMethodDeclaration(parent) ||
          ts.isPropertySignatureDeclaration(parent)) && parent.name === n)));
      const f = key || n === own ? undefined : byName.get(gate.local(n));
      if (f) found.add(f);
      return;
    }
    n.forEachChild((c) => mentioned(c, own, found));
  };
  const mentions = live.map((s) => {
    const found = new Set<FunctionDeclaration>();
    mentioned(s, ts.isFunctionDeclaration(s) ? s.name ?? null : null, found);
    return found;
  });
  for (let changed = true; changed;) {
    changed = false;
    live.forEach((s, i) => {
      const at = ts.isFunctionDeclaration(s) ? placed.get(s) ?? i : i;
      for (const f of mentions[i] ?? []) {
        const now = placed.get(f) ?? 0;
        if (at < now) {
          placed.set(f, at);
          changed = true;
        }
      }
    });
  }
  return placed;
}

/** The function declarations of a statement list, a function body's or a
 * block's (SOURCE-ELABORATION.md, "Function declarations in a body"), by
 * the index of the statement each is bound before (`functionPlacement`),
 * in source order there: each a constant bound to its closure; the first
 * `live` statements of `scope` may run, and a declaration placed past them
 * is never bound. A closure
 * mentioning one bound after it at the same place reads it as an early
 * binding (`markEarly`). Refused: a declaration of a `case` clause, whose
 * binding is the whole `switch` block's; one in a block of sloppy code,
 * which Annex B also assigns to a binding of the enclosing function when
 * the declaration is evaluated; an overloaded or repeated one; and one
 * naming a parameter of the function whose body holds it, which it
 * replaces there. */
export function functionDeclarations(this: Gate, scope: readonly Statement[], live: number, placed: Map<FunctionDeclaration, number>): Within<{ value: "any"; store: "grow" }, Map<number, Stmt[]>> {
  const gate: Gate = this;
  const declared = scope.filter((s): s is FunctionDeclaration => ts.isFunctionDeclaration(s));
  const bound = new Map<number, Stmt[]>();
  for (const s of declared) {
    const at = placed.get(s) ?? gate.fail(s, "a function declaration with no place");
    if (at >= live) continue;
    const holder = s.parent;
    if (!s.name) return gate.fail(s, "anonymous function");
    if (!holder || ts.isCaseClause(holder) || ts.isDefaultClause(holder))
      return gate.fail(s, "a function declaration in a `case` clause is outside the fragment: its binding is the whole `switch` block's");
    const owner = ts.isBlock(holder) && holder.parent && ts.isFunctionLikeDeclaration(holder.parent) &&
      holder.parent.body === holder ? holder.parent : null;
    if (!owner && !gate.strict)
      return gate.fail(s, "a function declaration in a block of sloppy code is outside the fragment: Annex B also binds it in the enclosing function");
    if (!s.body || declared.some((o) => o !== s && o.name?.text === s.name?.text))
      return gate.fail(s, "an overloaded or repeated function declaration in a body is outside the fragment");
    if (owner?.parameters.some((p) => ts.isIdentifier(p.name) && p.name.text === s.name?.text))
      return gate.fail(s.name, "a function declaration naming a parameter of its function is outside the fragment");
    if (s.name.text === "undefined")
      return gate.fail(s, "shadowing undefined is outside the fragment");
    bound.set(at, [...(bound.get(at) ?? []), { k: "const", pos: gate.span(s), bindings: [{ name: gate.local(s.name),
      namePos: gate.span(s.name), annot: null, init: gate.lambda(s), early: gate.earlyDecls.has(s) }] }]);
  }
  return bound;
}

/** A `type` or `interface` statement: TypeScript erases it, so it runs
 * nothing, wherever it is; it binds a type name over its block, which the
 * type readers resolve as TypeScript does (SOURCE-CONTRACTS.md,
 * "Block-scoped type declarations"). */
function typeStatement(s: Statement): Within<{ value: "any"; store: "grow" }, boolean> {
  return isTypeAlias(s) || ts.isInterfaceDeclaration(s);
}

/** The early bindings of a statement list (SOURCE-ELABORATION.md, "Lexical
 * bindings before initialization"): a one-name `let` or `const` of the list
 * one of whose mentions may run before the binding's initialization point,
 * the end of its declarator: a mention written before it, or one in a
 * closure created before it, which may run at any time after its creation.
 * A closure created after the point runs after it, in the same activation.
 * A function literal that is a constant's whole initializer runs only after
 * the constant holds it, so its mentions of the constant are the closure's
 * self entry. A pattern's binding so mentioned is refused. */
export function markEarly(this: Gate, live: readonly Statement[], placed: Map<FunctionDeclaration, number>): Within<{ value: "any"; store: "grow" }, void> {
  const gate: Gate = this;
  const functionLike = (n: Node): boolean => ts.isFunctionLikeDeclaration(n) || ts.isClassLikeDeclaration(n);
  const declared = new Map<string, ts.VariableDeclaration>();
  const patterns = new Map<string, ts.VariableDeclaration>();
  for (const st of live) {
    if (!ts.isVariableStatement(st)) continue;
    const list = st.declarationList;
    if (!(list.flags & (ts.NodeFlags.Let | ts.NodeFlags.Const))) continue;
    for (const d of list.declarations) {
      if (ts.isIdentifier(d.name)) declared.set(gate.local(d.name), d);
      else {
        const names = (b: ts.BindingName): void => {
          if (ts.isIdentifier(b)) patterns.set(gate.local(b), d);
          else for (const e of b.elements) if (!ts.isOmittedExpression(e) && e.name) names(e.name);
        };
        names(d.name);
      }
    }
  }
  // A function declaration is bound before the statement it is placed at
  // (`functionPlacement`), those placed together in source order: one
  // mentioned in the closure of one bound before it is early.
  const functions = [...placed.keys()];
  const order = new Map(functions.map((f, i) => [f.name ? gate.local(f.name) : "", i]));
  functions.forEach((f, i) => {
    const mention = (n: Node): void => {
      if (ts.isTypeNode(n)) return;
      if (ts.isIdentifier(n)) {
        const parent = n.parent;
        const key = !!parent && (((ts.isPropertyAccessExpression(parent) && parent.name === n) ||
          ((ts.isPropertyAssignment(parent) || ts.isMethodDeclaration(parent) ||
            ts.isPropertySignatureDeclaration(parent)) && parent.name === n)));
        const j = key || n === f.name ? undefined : order.get(gate.local(n));
        const later = j === undefined ? undefined : functions[j];
        if (j !== undefined && j > i && later && placed.get(later) === placed.get(f)) gate.earlyDecls.add(later);
        return;
      }
      n.forEachChild(mention);
    };
    mention(f);
  });
  if (!declared.size && !patterns.size) return;
  // `created` is where the outermost closure around a mention is created,
  // null outside one: a closure created after a binding's initialization
  // point runs after it, in the same activation.
  const visit = (n: Node, created: number | null): void => {
    if (ts.isTypeNode(n)) return;
    if (ts.isIdentifier(n)) {
      const parent = n.parent;
      const key = nameSlot(n) || (!!parent && ts.isPropertySignatureDeclaration(parent) && parent.name === n);
      const name = key ? undefined : gate.local(n);
      const at = created ?? n.getStart(gate.file);
      const d = name === undefined ? undefined : declared.get(name);
      if (d && n !== d.name && at < d.end) {
        let literal: Node | undefined = d.initializer;
        while (literal && ts.isParenthesizedExpression(literal)) literal = literal.expression;
        const self = !!(d.parent.flags & ts.NodeFlags.Const) && !!literal &&
          (ts.isArrowFunction(literal) || ts.isFunctionExpression(literal)) &&
          n.getStart(gate.file) >= literal.getStart(gate.file) && n.end <= literal.end;
        if (!self) gate.earlyDecls.add(d);
      }
      const p = name === undefined ? undefined : patterns.get(name);
      if (p && at < p.end && !(n.getStart(gate.file) >= p.name.getStart(gate.file) && n.end <= p.name.end))
        gate.fail(n, `a binding of a pattern read where it may be uninitialized is outside the fragment: ${n.text}`);
      return;
    }
    // A function declaration of the list is created where it is placed
    // (`functionPlacement`); one of a block nested in a statement, when
    // that block is entered, after the statement starts.
    const place = ts.isFunctionDeclaration(n) ? placed.get(n) : undefined;
    const inner = created ?? (place !== undefined ? live[place]?.getStart(gate.file) ?? -1
      : ts.isFunctionDeclaration(n) ? statementStart : functionLike(n) ? n.getStart(gate.file) : null);
    n.forEachChild((c) => visit(c, inner));
  };
  let statementStart = -1;
  for (const st of live) {
    statementStart = st.getStart(gate.file);
    visit(st, null);
  }
}

/** A statement, preceded by the statements its lowering runs before it:
 * the collection of a spread of a program's iterable (`collect`), or the
 * steps of an array pattern over one (`protocolPattern`). */
export function hoisting(this: Gate, s: Statement): Within<{ value: "any"; store: "grow" }, Stmt[]> {
  const gate: Gate = this;
  const savedHoist = gate.hoist, savedHoisted = gate.hoisted;
  let site: { entry(): Within<{ value: "any"; store: "grow" }, number>; span(): Within<{ value: "any"; store: "grow" }, Span> } | null = null;
  const lazy = () => site ??= gate.sites(s);
  gate.hoist = { stmt: s, spread: gate.hoistTarget(s),
    site: { entry: () => lazy().entry(), span: () => lazy().span() } };
  gate.hoisted = [];
  try {
    // A list of several declarators, a pattern among them, binds each in
    // turn, its initializer seeing the earlier bindings: each is lowered as
    // a declaration of its own, preceded by the statements its own lowering
    // runs before it, in the list's order.
    // A `var` list is not this binding form: `declarations` refuses it.
    const list = ts.isVariableStatement(s) ? s.declarationList : null;
    if (list && list.flags & (ts.NodeFlags.Const | ts.NodeFlags.Let) &&
        list.declarations.length > 1 && list.declarations.some((d) => !ts.isIdentifier(d.name))) {
      const parts: Stmt[] = [];
      list.declarations.forEach((d, i) => {
        gate.hoisted = [];
        const part = gate.declarator(list, d, s, i === 0 ? gate.span(s) : gate.span(d));
        parts.push(...gate.hoisted, ...part);
      });
      return parts;
    }
    const stmts = (ts.isVariableStatement(s) ? gate.letPattern(s) : null) ?? [gate.stmt(s)];
    return [...this.hoisted, ...stmts];
  } finally {
    gate.hoist = savedHoist;
    gate.hoisted = savedHoisted;
  }
}

/** `let pattern = init;` whose bindings are written: the pattern binds
 * names no source spells, as a `const` pattern binds, then a `let` binds
 * each of the source's names to its value, a cell of its own whose
 * contract is as an unannotated `let`'s, its initializer's type widened.
 * JavaScript reads and defaults the pattern's positions, then initializes
 * the bindings, in the same order either way. Each cell is claimed at its
 * name, as the value it starts with is. Null for any other statement. */
export function letPattern(this: Gate, s: ts.VariableStatement): Within<{ value: "any"; store: "grow" }, Stmt[] | null> {
  const gate: Gate = this;
  const list = s.declarationList;
  const [d] = list.declarations;
  if (list.flags & ts.NodeFlags.Const || !(list.flags & ts.NodeFlags.Let) || list.declarations.length !== 1 ||
      !d || !(ts.isObjectBindingPattern(d.name) || ts.isArrayBindingPattern(d.name)) || gate.neverAssigned(list))
    return null;
  return gate.letPatternOf(d, gate.span(s));
}

/** The declarator `d` of a `let` list whose bindings are written, a
 * pattern, as `letPattern` lowers it, its destructuring at `pos`. Null over
 * a program's iterable. */
export function letPatternOf(this: Gate, d: ts.VariableDeclaration, pos: Span): Within<{ value: "any"; store: "grow" }, Stmt[] | null> {
  const gate: Gate = this;
  if (d.type)
    gate.fail(d, "an annotated `let` pattern whose bindings are assigned is outside the fragment: each binding's contract is the part of the annotation it reads, which the lowering does not state");
  if (!d.initializer) gate.fail(d, "a `let` pattern needs an initializer");
  // Over a program's iterable, an array pattern is the iterator's steps
  // (`protocolPattern`), which bind no cells.
  if (ts.isArrayBindingPattern(d.name) &&
      gate.iterations.get(gate.span(d.initializer).join(":"))?.startsWith("client"))
    return null;
  const target = gate.pattern(d.name, new Set(), ts.isArrayLiteralExpression(skipParentheses(d.initializer)));
  gate.initializedBefore(d, [[target, null]]);
  return writtenPattern(pos, gate.span(d.name), target, null, gate.expr(d.initializer), null);
}

/** A pattern whose bindings are written, destructured at `pos`: the
 * pattern binds names no source spells, as a `const` pattern binds, then a
 * `let` at `letPos` binds each of the source's names to its value, a cell
 * of its own. `annot` is a lone name's contract; absent, a binding's
 * contract is as an unannotated `let`'s. */
export function writtenPattern(pos: Span, letPos: Span, target: PatternAst, default_: Expr | null, init: Expr,
    annot: TypeTerm | null): Stmt[] {
  const cells: BindingAst[] = [];
  const hide = (t: PatternAst): PatternAst => {
    switch (t.k) {
      case "name": {
        const hidden = `%let-pattern ${t.name}`;
        cells.push({ early: false, name: t.name, namePos: t.pos, annot: target.k === "name" ? annot : null,
          init: { k: "id", pos: t.pos, name: hidden } });
        return { ...t, name: hidden };
      }
      case "object": return { ...t, props: t.props.map((q) => ({ ...q, target: hide(q.target) })),
        rest: t.rest ? { ...t.rest, target: hide(t.rest.target) } : null };
      case "array": return { ...t, elems: t.elems.map((q) => ({ ...q, target: hide(q.target) })),
        rest: t.rest ? { ...t.rest, target: hide(t.rest.target) } : null };
    }
  };
  const hidden = hide(target);
  return [
    { k: "destructure", pos, target: hidden, default_, init },
    { k: "let", pos: letPos, bindings: cells },
  ];
}

/** A parameter `at`, written as a pattern or with a default: a
 * `destructure` at `pos` over its hidden name, binding the source's names,
 * the default replacing an undefined argument. A parameter is a mutable
 * binding: where a write within `scope`, the function, names one of its
 * bindings, a lone name is a cell as a written `let` pattern's binding
 * (`writtenPattern`), its contract its annotation `annot`. A pattern's
 * bindings written, or a lone name without an annotation, are refused:
 * neither the contract of each binding the annotation implies nor the
 * binding of each name before the pattern's later defaults read it is
 * lowered. */
export function parameterBinding(this: Gate, at: Node, scope: Node, pos: Span, target: PatternAst,
    default_: Expr | null, hidden: string, annot: TypeTerm | null): Within<{ value: "any"; store: "grow" }, Stmt[]> {
  const gate: Gate = this;
  if (!writesName(gate, scope, new Set(patternNames(target))))
    return [{ k: "destructure", pos, target, default_, init: { k: "id", pos: target.pos, name: hidden } }];
  if (target.k !== "name")
    gate.fail(at, "a parameter pattern whose bindings are assigned is outside the fragment: each binding's contract is the part of the parameter's annotation it reads, and each is bound where the pattern reaches it, before a later default reads it, neither of which is lowered");
  if (annot === null)
    gate.fail(at, "an assigned parameter with a default and no annotation is outside the fragment: its contract is the type its context gives, which is not lowered");
  // The hidden name is read at the whole parameter, a site apart from the
  // name, which the `let` reads the pattern's hidden name at.
  return writtenPattern(pos, target.pos, target, default_, { k: "id", pos, name: hidden }, annot);
}

/** The offset of `token` at or after `from`, past whitespace and comments:
 * a punctuator or keyword of `at` the tree has no node for. */
export function token(this: Gate, from: number, token: string, at: Node): Within<{ value: "any"; store: "grow" }, number> {
  const gate: Gate = this;
  const text = gate.file.text;
  let i = from;
  for (;;) {
    if (/\s/.test(text[i] ?? "")) i++;
    else if (text.startsWith("//", i)) {
      const n = text.indexOf("\n", i);
      i = n < 0 ? text.length : n;
    } else if (text.startsWith("/*", i)) {
      const n = text.indexOf("*/", i + 2);
      i = n < 0 ? text.length : n + 2;
    } else break;
  }
  if (!text.startsWith(token, i)) gate.fail(at, `expected \`${token}\``);
  return i;
}

/** `for (init; cond; update) body`: `init`, then the loop whose head tests
 * `cond` (`true` where it is absent, at the second `;`) and whose body's
 * end and every `continue` run `update`; with an `init`, in a block of its
 * own, the loop's entry at the first `;` (a block has none, and the `init`
 * statement's is at its start). A `let` declared there is one
 * binding for the whole loop, where
 * JavaScript copies it into each iteration: the two differ only for a
 * closure capturing it, where the loop is lowered with a binding per
 * iteration (`perIterationFor`). */
export function forStmt(this: Gate, node: ts.ForStatement): Within<{ value: "any"; store: "grow" }, Stmt> {
  const gate: Gate = this;
  if (capturesLoopLet(node)) return gate.perIterationFor(node);
  const open = gate.token(node.getStart(gate.file) + "for".length, "(", node);
  const init = node.initializer;
  const first = gate.token(init ? init.end : open + 1, ";", node);
  const second = gate.token(node.condition ? node.condition.end : first + 1, ";", node);
  let initial: Stmt | null = null;
  if (init && ts.isVariableDeclarationList(init)) {
    initial = gate.declarations(init, init);
  } else if (init && ts.isExpression(init)) initial = { k: "effect", pos: gate.span(init), e: gate.expr(init) };
  else if (init) gate.fail(init, "a `for` initializer is a declaration or an expression");
  const loop: Stmt = {
    k: "while",
    pos: init ? [first, node.end] : gate.span(node),
    cond: node.condition
      ? gate.expr(node.condition)
      : { k: "lit", pos: [second, second + 1], lit: { a: "booleanlit", v: "true" } },
    body: gate.loopBody(node),
    update: node.incrementor
      ? [{ k: "effect", pos: gate.span(node.incrementor), e: gate.expr(node.incrementor) }]
      : [],
  };
  return initial ? { k: "block", pos: gate.span(node), label: null, body: [initial, loop] } : loop;
}

/** `for (let x̄ = ē; c; u) s` with a binding per iteration, as JavaScript's
 * ForBodyEvaluation runs it (CreatePerIterationEnvironment): the head's
 * bindings `x̄⁰`, which `ē` and its closures see; carriers `x̄ᶜ` holding
 * their values between iterations; and in each iteration fresh bindings
 * `x̄` initialized from the carriers, the update run on them from the
 * second iteration on, then the test, then the body in a block a
 * `continue` of the loop leaves, then the carriers set from them:
 *
 *     { let x̄⁰ = ē; let x̄ᶜ = x̄⁰, %stepped = false;
 *       while (true) {
 *         let x̄ = x̄ᶜ;
 *         if (%stepped) u; else %stepped = true;
 *         if (c) {} else break;
 *         ℓ: { s }
 *         x̄ᶜ = x̄;
 *       } }
 *
 * `%stepped` is present only with an update. `x̄⁰` and `x̄ᶜ` are names no
 * source spells; the mentions of the head's names in `ē` read `x̄⁰`, and
 * those in `c`, `u` and `s` read `x̄`. The added statements' sites are the
 * free offsets of the head (`sites`). */
export function perIterationFor(this: Gate, node: ts.ForStatement): Within<{ value: "any"; store: "grow" }, Stmt> {
  const gate: Gate = this;
  const init = node.initializer;
  if (!init || !ts.isVariableDeclarationList(init)) return gate.fail(node, "internal: a `for` head with a binding per iteration and no `let`");
  const s = node.getStart(gate.file);
  const names: string[] = [];
  for (const d of init.declarations) {
    if (!ts.isIdentifier(d.name))
      gate.fail(d.name, "a `let` pattern in a `for` head a closure captures is outside the fragment");
    names.push(gate.local(d.name));
  }
  const declared = new Set(names);
  const initial = (n: string): string => `%initial@${s}%${n}`;
  const carrier = (n: string): string => `%carrier@${s}%${n}`;
  const stepped = `%stepped@${s}`;
  const rename = (n: Node): void => {
    if (ts.isTypeNode(n)) return;
    if (ts.isIdentifier(n) && !nameSlot(n)) {
      const local = gate.local(n);
      if (declared.has(local)) gate.renames.set(`${n.getStart(gate.file)}:${n.end}`, initial(local));
    }
    n.forEachChild(rename);
  };
  rename(init);
  const head = gate.declarations(init, init);
  if (head.k !== "let") return gate.fail(init, "internal: a `for` head's `let` lowered to another declaration");
  const annots = new Map(head.bindings.map((b) => [b.name, b.annot]));
  const site = gate.sites(node, node.statement.getStart(gate.file));
  const entry = (): Span => {
    const e = site.entry();
    return [e, e + 1];
  };
  const id = (name: string): Expr => ({ k: "id", pos: site.span(), name });
  const lit = (v: "true" | "false"): Expr => ({ k: "lit", pos: site.span(), lit: { a: "booleanlit", v } });
  const assign = (name: string, rhs: Expr): Stmt =>
    ({ k: "effect", pos: entry(), e: { k: "assign", pos: site.span(), name, namePos: site.span(), rhs } });
  const binding = (name: string, annot: TypeTerm | null, init: Expr): BindingAst =>
    ({ early: false, name, namePos: site.span(), annot, init });
  const carriers: Stmt = { k: "let", pos: entry(), bindings: [
    ...names.map((n) => binding(carrier(n), annots.get(initial(n)) ?? null, id(initial(n)))),
    ...(node.incrementor ? [binding(stepped, null, lit("false"))] : [])] };
  const loopPos = entry();
  const iteration: Stmt[] = [
    { k: "let", pos: entry(), bindings: names.map((n) => binding(n, annots.get(initial(n)) ?? null, id(carrier(n)))) },
  ];
  if (node.incrementor)
    iteration.push({ k: "if", pos: entry(), cond: id(stepped),
      then: [{ k: "effect", pos: gate.span(node.incrementor), e: gate.expr(node.incrementor) }],
      else_: [assign(stepped, lit("true"))] });
  if (node.condition)
    iteration.push({ k: "if", pos: entry(), cond: gate.expr(node.condition), then: [],
      else_: [{ k: "break", pos: entry(), label: null }] });
  iteration.push({ k: "block", pos: entry(), label: iterationLabel(node, gate.file), body: gate.block(node.statement) });
  for (const n of names) iteration.push(assign(carrier(n), id(n)));
  const loop: Stmt = { k: "while", pos: loopPos, cond: lit("true"), body: iteration, update: [] };
  return { k: "block", pos: gate.span(node), label: null, body: [head, carriers, loop] };
}

/** `for (const k in o) body` is `for (const k of %ForIn%(o)) body`: the
 * keys the loop visits, a string each (`intrinsics.mts`), the call at the
 * declaration, the intrinsic read at `in`. */
export function forInStmt(this: Gate, node: ts.ForInStatement): Within<{ value: "any"; store: "grow" }, Stmt> {
  const gate: Gate = this;
  const list = node.initializer;
  if (!ts.isVariableDeclarationList(list) || list.declarations.length !== 1 ||
      !(list.flags & ts.NodeFlags.Const || (list.flags & ts.NodeFlags.Let && gate.neverAssigned(list, true))))
    gate.fail(node, "a `for...in` loop declares one `const` binding, or a `let` nothing assigns");
  const d = list.declarations[0];
  if (!ts.isIdentifier(d.name)) gate.fail(d, "destructuring is outside the fragment");
  if (d.type || d.initializer) gate.fail(d, "a `for...in` binding takes the key's type");
  if (d.name.text === "undefined") gate.fail(d, "shadowing undefined is outside the fragment");
  const keyword = gate.token(list.end, "in", node);
  // A body reading the entry at the key before anything can change it
  // steps the entries: the key is the step's first element, each such read
  // its second.
  const reads = forInEntryReads(node);
  if (reads.length) {
    const entry = `%for-in@${node.getStart(gate.file)}%`;
    for (const read of reads) gate.entryReads.set(gate.span(read).join(":"), entry);
    // The entry is bound at the head's declaration, the key at its name
    // from the entry's first element, read at `in`.
    const [start] = gate.span(list);
    return {
      k: "forOf",
      pos: gate.span(node),
      name: entry,
      namePos: gate.span(list),
      iterate: iterateForInName,
      iterable: gate.expr(node.expression),
      body: [
        { k: "const", pos: [start, start + 1], bindings: [{ early: false, name: gate.local(d.name), namePos: gate.span(d.name),
          annot: null, init: { k: "index", pos: [keyword, keyword + "in".length],
            e: { k: "id", pos: [keyword, keyword + 1], name: entry },
            key: { k: "lit", pos: [keyword + 1, keyword + 2], lit: { a: "numberlit", v: "0" } } } }] },
        ...this.block(node.statement),
      ],
    };
  }
  return {
    k: "forOf",
    pos: gate.span(node),
    name: gate.local(d.name),
    namePos: gate.span(d.name),
    iterate: iterateName,
    iterable: gate.intrinsic(forInName, gate.span(list), [keyword, keyword + "in".length],
      [gate.expr(node.expression)]),
    body: gate.loopBody(node),
  };
}

/** The destructuring of a pattern binding a `for...of`, `const p = %element`,
 * which each iteration runs first, before the body: a `const` pattern
 * statement's over a value another reference may hold (an array's loop
 * reads its element in place, and a program's iterator may keep what it
 * yields), at the entry `pos`, its read of the element at `at`. */
export function forOfPattern(this: Gate, d: ts.VariableDeclaration, name: ts.BindingPattern, element: string,
    pos: Span, at: Span): Within<{ value: "any"; store: "grow" }, Stmt> {
  const gate: Gate = this;
  const target = gate.pattern(name, new Set(), false);
  gate.initializedBefore(d, [[target, null]]);
  return { k: "destructure", pos, target, default_: null, init: { k: "id", pos: at, name: element } };
}

/** `for (const x of e) S` over an iterable the program defines, an object
 * with its own `[Symbol.iterator]`, as ECMA-262's ForIn/OfBodyEvaluation
 * runs it: GetIterator, then IteratorStepValue until done, the body per
 * value, and IteratorClose where the body is left otherwise than by
 * completing or by a `continue` of the loop. In ordinary forms, under
 * names no source spells:
 *
 *     const %iterator = e[Symbol.iterator](), %next = %iterator.next.bind(%iterator);
 *     while (true) {
 *       const %result = %next();
 *       if (%result.done) break;
 *       const x = %result.value;      // a pattern p: const %element = %result.value;
 *       closing { S } close {         //   closing { const p = %element; S } close …
 *         const %return = %iterator.return;
 *         if (typeof %return !== "undefined") { const %closed: object = %return.call(%iterator); }
 *       }
 *     }
 *
 * `next` is read once, as GetIterator reads it, and called on the iterator
 * at each step (a bound function is that call). The `closing` region runs
 * `close` before a `break` of the loop leaves it, before a `return` returns,
 * and, its own throws discarded, before a throw out of the body resumes
 * (IteratorClose with a throw completion); a `continue` and the body's end
 * go to the next step, and a done result leaves without it. `return`
 * absent (`undefined`) is not called; its result must be an object, the
 * TypeError IteratorClose throws otherwise being then impossible. Each part
 * has a claim site of its own: a token of the header or a run of them. */
export function protocolForOf(this: Gate, node: ts.ForOfStatement, list: ts.VariableDeclarationList,
    name: ts.BindingName, method: boolean): Within<{ value: "any"; store: "grow" }, Stmt> {
  const gate: Gate = this;
  const s = node.getStart(gate.file);
  const p = gate.token(s + "for".length, "(", node);
  const c = list.getStart(gate.file);
  const [n0, n1] = gate.span(name);
  const o = gate.token(list.end, "of", node);
  const [e0, e1] = gate.span(node.expression);
  const q = gate.token(e1, ")", node);
  const end = node.end;
  const iterator = `%iterator@${s}`, next = `%next@${s}`, result = `%result@${s}`;
  const id = (pos: Span, name: string): Expr => ({ k: "id", pos, name });
  const iteratorAt = (): Expr => id([q, q + 1], iterator);
  const symbol = gate.wellKnownIterator;
  if (symbol === null) gate.fail(node, "a program's iterable needs the well-known `Symbol.iterator`, which the declarations do not list");
  const getIterator: Expr = { k: "invoke", pos: [o, e1], args: [],
    callee: { k: "read", pos: [o, o + "of".length], field: { symbol }, e: gate.expr(node.expression) } };
  const nextBound: Expr = { k: "bindWithReceiver", pos: [s, q + 1], args: [],
    callee: { k: "read", pos: [p, q + 1], field: "next", e: iteratorAt() }, receiver: iteratorAt() };
  // The close's sites: the header's runs of tokens the steps do not use,
  // each list read in order at its own counter.
  const entries = [o, o + 1, q];
  const spans: Span[] = [[n0, e1], [s, end], [e0, q + 1], [o, q + 1], [c, q + 1], [p, e1]];
  let nextEntry = 0;
  let nextSpan = 0;
  const close = gate.closeStatements(iteratorAt, `${s}`, {
    entry: () => entries[nextEntry++] ?? gate.fail(node, "internal: the close's entries"),
    span: () => spans[nextSpan++] ?? gate.fail(node, "internal: the close's sites"),
  }, method);
  // A pattern binds the step's value to a name no source spells, and
  // destructures it first in the closing region: ForIn/OfBodyEvaluation
  // initializes the pattern after IteratorValue and before the body, and
  // closes the iterator on its abrupt completion. The destructuring is a
  // `const` pattern statement's over a value another reference may hold.
  // Its entry is the keyword's fourth offset and its read of the value the
  // run from the keyword to the pattern; in a compact head (`let[x]`) these
  // meet the pattern's own spans, and the execution points the claims are
  // attached to (`checkPointSites`) keep them apart.
  const bound = ts.isIdentifier(name) ? gate.local(name) : `%element@${c}`;
  const [d] = list.declarations;
  if (!d) return gate.fail(node, "internal: a `for...of` head without its declaration");
  const destructure: Stmt[] = ts.isIdentifier(name) ? []
    : [gate.forOfPattern(d, name, bound, [c + 3, c + 4], [c, n0])];
  const step: Stmt[] = [
    { k: "const", pos: [c, c + "const".length], bindings: [{ early: false, name: result, namePos: [c, c + "const".length],
      annot: null, init: { k: "apply", pos: [s, s + "for".length], callee: id([c, e1], next), args: [] } }] },
    { k: "if", pos: [c + 1, c + 2],
      cond: { k: "read", pos: [c, c + "const".length], field: "done", e: id([p, p + 1], result) },
      then: [{ k: "break", pos: [c + 2, c + 3], label: null }], else_: null },
    { k: "const", pos: [n0, n1], bindings: [{ early: false, name: bound, namePos: [n0, n1], annot: null,
      init: { k: "read", pos: [n0, n1], field: "value", e: id([c, n1], result) } }] },
    { k: "closing", pos: [s + 1, s + 2], close, body: [...destructure, ...gate.loopBody(node)] },
  ];
  return { k: "block", pos: gate.span(node), label: null, body: [
    { k: "const", pos: [s, s + "for".length], bindings: [
      { early: false, name: iterator, namePos: [s, s + "for".length], annot: null, init: getIterator },
      { early: false, name: next, namePos: [p, p + 1], annot: null, init: nextBound }] },
    { k: "while", pos: [p, end], cond: { k: "lit", pos: [s, p + 1], lit: { a: "booleanlit", v: "true" } },
      body: step, update: [] },
  ] };
}

/** Claim sites for the parts a lowering adds to the statement `within`:
 * the offsets from its start up to the next token after it at which no node
 * of it starts and that lie in no function nested in it, whose statements
 * have sites of their own. Each is an entry once (`entry`), and the spans
 * from them are expression sites (`span`); none is a source node's site.
 * With `until`, only the offsets before it are entries and starts of
 * spans. */
export function sites(this: Gate, within: Node, until?: number): Within<{ value: "any"; store: "grow" }, { entry(): Within<{ value: "any"; store: "grow" }, number>; span(): Within<{ value: "any"; store: "grow" }, Span> }> {
  const gate: Gate = this;
  const text = gate.file.text;
  let to = within.end;
  while (to < text.length && /\s/.test(text[to] ?? "")) to++;
  const free = freeOffsets(within, gate.file).filter((o) => until === undefined || o < until);
  let entries = 0, from = 0, end = 0;
  return {
    entry: () => {
      const o = free[entries++];
      if (o === undefined) return gate.fail(within, "too few claim sites in the statement for the iterator protocol it runs");
      return o;
    },
    span: () => {
      for (;;) {
        const a = free[from];
        if (a === undefined) return gate.fail(within, "too few claim sites in the statement for the iterator protocol it runs");
        if (end === 0) end = a;
        if (++end <= to) return [a, end];
        from++;
        end = 0;
      }
    },
  };
}

/** GetIterator on a program's iterable, as `protocolForOf` does it: the
 * declarators `%iterator = iterable[Symbol.iterator](), %next =
 * %iterator.next.bind(%iterator)`, `next` read once and called on the
 * iterator at each step (`protocolStep`). */
export function protocolStart(this: Gate, iterable: Expr, site: { entry(): Within<{ value: "any"; store: "grow" }, number>; span(): Within<{ value: "any"; store: "grow" }, Span> }, tag: string, at: Node):
    Within<{ value: "any"; store: "grow" }, { bindings: BindingAst[]; iterator: string; next: string; iteratorAt: () => Within<{ value: "any"; store: "grow" }, Expr> }> {
  const gate: Gate = this;
  const iterator = `%iterator@${tag}`, next = `%next@${tag}`;
  const symbol = gate.wellKnownIterator;
  if (symbol === null)
    return gate.fail(at, "a program's iterable needs the well-known `Symbol.iterator`, which the declarations do not list");
  const iterAt = site.span();
  const iteratorAt = (): Expr => ({ k: "id", pos: iterAt, name: iterator });
  const call = site.span(), method = site.span(), bound = site.span(), nextRead = site.span();
  return {
    iterator, next, iteratorAt,
    bindings: [
      { early: false, name: iterator, namePos: call, annot: null, init: { k: "invoke", pos: call, args: [],
        callee: { k: "read", pos: method, field: { symbol }, e: iterable } } },
      { early: false, name: next, namePos: bound, annot: null, init: { k: "bindWithReceiver", pos: bound, args: [],
        callee: { k: "read", pos: nextRead, field: "next", e: iteratorAt() }, receiver: iteratorAt() } },
    ],
  };
}

/** One step of the protocol, `%next()`, bound to `result`, and the test of
 * its `done`, which leaves by `leave`: three statements, with their
 * entries. The value is `result`'s `value`, read by the caller next. */
export function protocolStep(this: Gate, next: string, result: string, leave: () => Within<{ value: "any"; store: "grow" }, Stmt>,
    site: { entry(): Within<{ value: "any"; store: "grow" }, number>; span(): Within<{ value: "any"; store: "grow" }, Span> }): Within<{ value: "any"; store: "grow" }, { stmts: Stmt[]; value: () => Within<{ value: "any"; store: "grow" }, Expr> }> {
  const nextAt = site.span();
  const e1 = site.entry();
  const call: Expr = { k: "apply", pos: site.span(), callee: { k: "id", pos: nextAt, name: next }, args: [] };
  const e2 = site.entry();
  const doneRead: Expr = { k: "read", pos: site.span(), field: "done", e: { k: "id", pos: site.span(), name: result } };
  const valueAt = site.span(), resultAt = site.span();
  return {
    stmts: [
      { k: "const", pos: [e1, e1 + 1], bindings: [{ early: false, name: result, namePos: call.pos, annot: null, init: call }] },
      { k: "if", pos: [e2, e2 + 1], cond: doneRead, then: [leave()], else_: null },
    ],
    value: () => ({ k: "read", pos: valueAt, field: "value", e: { k: "id", pos: resultAt, name: result } }),
  };
}

/** `switch (d) { clauses }`, as labeled blocks, one per clause, nested in
 * source order inside one for the whole switch. The innermost holds the
 * dispatch: it tests the discriminant with `===` against each case label
 * in source order, a match leaving the block of that label's clause, and
 * with every test failed leaves the block of `default`, or the switch's.
 * Each clause's statements follow its block's end, inside the next clause's
 * block, so a clause that completes runs on into the next one's statements,
 * as JavaScript falls through; a `break` leaves the switch's block. A
 * discriminant that is a name, or a field of a name, is read again at each
 * test, at the `case` keyword (the name of a field's object at its first
 * character), when the switch has a `case` test, so that the first test
 * reads it where JavaScript evaluates it, and every label is a literal, a name or an enum's member,
 * since then nothing between the tests writes and a field is a plain
 * location; each test then narrows the name, or the object's arms, as an
 * `if` does. A discriminant `typeof d`, `d` such a name or field, is read
 * again the same way, each test `typeof d === l`, the `typeof` test of `d`
 * where `l` is a string `typeof` answers. Any other is
 * evaluated first and bound to a name no source can spell. Every span is a node or a token: a test's `if`
 * begins at `case`, its read of the discriminant is at `case`, its `===`
 * at the clause's `:`, and its jump at the label; the jump to `default` is
 * at the keyword, the one to the switch's end at the clauses' `{`. The clauses
 * share one scope in JavaScript, so a name one declares directly must not
 * be read in another clause or in a label. */
export function switchStmt(this: Gate, node: ts.SwitchStatement): Within<{ value: "any"; store: "grow" }, Stmt> {
  const gate: Gate = this;
  const clauses = node.caseBlock.clauses;
  for (const c of clauses) {
    const declared = new Set<string>();
    const collect = (n: Node): void => {
      if (ts.isIdentifier(n)) declared.add(n.text);
      else n.forEachChild(collect);
    };
    for (const s of c.statements) {
      if (ts.isVariableStatement(s)) for (const d of s.declarationList.declarations) collect(d.name);
      else if (ts.isClassDeclaration(s) && s.name) declared.add(s.name.text);
    }
    if (!declared.size) continue;
    const refers = (n: Node): Node | undefined =>
      ts.isIdentifier(n) && declared.has(n.text) ? n : n.forEachChild(refers);
    for (const other of clauses) {
      const at = (ts.isCaseClause(other) ? refers(other.expression) : undefined) ??
        (other === c ? undefined : other.statements.map(refers).find((n) => n));
      if (at) gate.fail(at, "a name declared in one switch clause and read in another is outside the fragment");
    }
  }
  const unwrap = (e: Expression): Expression => (ts.isParenthesizedExpression(e) ? unwrap(e.expression) : e);
  // A member of an enum, `E.M` or `ns.E.M`, a host family's tag enum
  // (`ts.SyntaxKind`) included: a read of a data field of the enum's object,
  // which writes nothing.
  const enumLabel = (u: Expression): boolean => {
    if (!ts.isPropertyAccessExpression(u) || u.questionDotToken) return false;
    if (gate.constEnumReads.has(gate.span(u).join(":"))) return true;
    const base = u.expression;
    const enumName = ts.isIdentifier(base) ? gate.local(base) : gate.namespaceMember(base);
    if (enumName === undefined) return false;
    const member = u.name.text;
    return (gate.enums.has(enumName) && gate.enumMembers(enumName).some((m) => m.name === member)) ||
      !!gate.importedEnums.get(enumName)?.members.some((m) => m.name === member);
  };
  const plain = (e: Expression): boolean => {
    const u = unwrap(e);
    return ts.isIdentifier(u) || ts.isStringLiteral(u) || ts.isNumericLiteral(u) ||
      u.kind === ts.SyntaxKind.TrueKeyword || u.kind === ts.SyntaxKind.FalseKeyword ||
      u.kind === ts.SyntaxKind.NullKeyword ||
      (ts.isPrefixUnaryExpression(u) && u.operator === ts.SyntaxKind.MinusToken && ts.isNumericLiteral(u.operand)) ||
      enumLabel(u);
  };
  const outer = unwrap(node.expression);
  // `switch (typeof x)`: each test is the `typeof` test of `x` read again.
  const typeofOf = ts.isTypeOfExpression(outer) ? outer : null;
  const discriminant = typeofOf ? unwrap(typeofOf.expression) : outer;
  const bound: Stmt[] = [];
  let name: string;
  const fieldOf = ts.isPropertyAccessExpression(discriminant) && !discriminant.questionDotToken &&
    ts.isIdentifier(discriminant.expression) &&
    !gate.staticReads.has(gate.span(discriminant.name).join(":"))
    ? { object: gate.local(discriminant.expression), field: discriminant.name.text } : null;
  // With no `case` test, nothing would read the discriminant again, so it
  // is evaluated once: JavaScript evaluates it before any clause, and that
  // may throw (a name before its initialization).
  const reread = clauses.some((c) => ts.isCaseClause(c)) &&
    clauses.every((c) => !ts.isCaseClause(c) || plain(c.expression)) &&
    (!typeofOf || ts.isIdentifier(discriminant) || fieldOf !== null);
  if (ts.isIdentifier(discriminant) && reread) name = gate.local(discriminant);
  else if (fieldOf && reread) name = fieldOf.object;
  else {
    name = `%switch@${node.getStart(gate.file)}%`;
    const at = gate.span(node.expression);
    bound.push({ k: "const", pos: at, bindings: [{ early: false, name, namePos: at, annot: null, init: gate.expr(node.expression) }] });
  }
  const end = switchLabel(node, gate.file);
  const label = (c: ts.CaseOrDefaultClause): string => `%case@${c.getStart(gate.file)}%`;
  const dispatch: Stmt[] = [];
  let fallback: Stmt | null = null;
  for (const c of clauses) {
    const start = c.getStart(gate.file);
    if (!ts.isCaseClause(c)) {
      fallback = { k: "break", pos: [start, start + "default".length], label: label(c) };
      continue;
    }
    const colon = gate.token(c.expression.end, ":", c);
    const read: Expr = fieldOf && reread
      ? { k: "read", pos: [start, start + "case".length], field: fieldOf.field,
          e: { k: "id", pos: [start, start + 1], name } }
      : { k: "id", pos: [start, start + "case".length], name };
    const written = unwrap(c.expression);
    const shape = typeofOf && reread && ts.isStringLiteral(written)
      ? TYPEOF_SHAPES.find((t) => t === written.text) : undefined;
    const cond: Expr = shape
      ? { k: "typeofTest", pos: [colon, colon + 1], shape, equal: true, e: read }
      : { k: "bin", pos: [colon, colon + 1], op: "===",
          l: typeofOf && reread ? { k: "unary", op: "typeof", pos: [start, start + "case".length], e: read } : read,
          r: gate.expr(c.expression) };
    dispatch.push({ k: "if", pos: [start, c.expression.end], cond,
      then: [{ k: "break", pos: gate.span(c.expression), label: label(c) }], else_: null });
  }
  const open = node.caseBlock.getStart(gate.file);
  dispatch.push(fallback ?? { k: "break", pos: [open, open + 1], label: end });
  const body = clauses.reduce<Stmt[]>((inner, c): Stmt[] =>
    [{ k: "block", pos: gate.span(c), label: label(c), body: inner }, ...this.statements(c.statements)], dispatch);
  return { k: "block", pos: gate.span(node), label: end, body: [...bound, ...body] };
}

/** `try { … } catch (e) { … } finally { … }`. The caught value is
 * `unknown`, the only annotation admitted: anything may be thrown. The
 * finalizer runs on every way out of the body and the handler, which the
 * lowering states by running it on each (`SourceExtraction`). */
export function tryStmt(this: Gate, node: ts.TryStatement): Within<{ value: "any"; store: "grow" }, Stmt> {
  const gate: Gate = this;
  const handler = node.catchClause;
  let param: { name: string; namePos: Span } | null = null;
  const d = handler?.variableDeclaration;
  if (d) {
    if (!ts.isIdentifier(d.name)) gate.fail(d, "destructuring is outside the fragment");
    if (d.type && d.type.kind !== ts.SyntaxKind.UnknownKeyword)
      gate.fail(d.type, "a caught value is `unknown`");
    if (d.name.text === "undefined") gate.fail(d, "shadowing undefined is outside the fragment");
    param = { name: gate.local(d.name), namePos: gate.span(d.name) };
  }
  return {
    k: "try",
    pos: gate.span(node),
    body: gate.statements(node.tryBlock.statements),
    handler: handler ? { param, body: gate.statements(handler.block.statements) } : null,
    finalizer: node.finallyBlock ? gate.statements(node.finallyBlock.statements) : null,
  };
}

/** Whether a statement never completes normally: a jump, or a list or both
 * arms of an `if` that reach one. A loop may complete. */
export function abrupt(s: Statement): Within<{ value: "any"; store: "grow" }, boolean> {
  return ts.isReturnStatement(s) || ts.isBreakStatement(s) || ts.isContinueStatement(s) ||
    ts.isThrowStatement(s) ||
    (ts.isBlock(s) && s.statements.some((t) => abrupt(t))) ||
    (ts.isIfStatement(s) && !!s.elseStatement && abrupt(s.thenStatement) && abrupt(s.elseStatement)) ||
    // A `try` completes through its body or handler, then its `finally`.
    (ts.isTryStatement(s) && ((!!s.finallyBlock && abrupt(s.finallyBlock)) ||
      (abrupt(s.tryBlock) && (!s.catchClause || abrupt(s.catchClause.block)))));
}

export function stmt(this: Gate, node: Statement): Within<{ value: "any"; store: "grow" }, Stmt> {
  const gate: Gate = this;
  // `assert(v, m);` of `node:assert/strict`, which the declaration graph
  // found to be the reviewed one, with no message or a literal one: the
  // calculus's own test, `if (!v) throw %AssertionFailure%(m)`. The literal
  // is evaluated after `v`, with nothing observable between.
  if (ts.isExpressionStatement(node) && ts.isCallExpression(node.expression) &&
      gate.assertionCalls.has(gate.span(node.expression).join(":"))) {
    const call = node.expression;
    const [value, message] = call.arguments;
    if (!value) return gate.fail(call, "an assertion of no value");
    const callee = call.expression;
    const failure = gate.intrinsic(assertionFailureName, gate.span(callee), [callee.end, callee.end + 1],
      message ? [gate.expr(message)] : []);
    return { k: "if", pos: gate.span(node), cond: { k: "not", pos: gate.span(call), e: gate.expr(value) },
      then: [{ k: "throw", pos: gate.span(callee), e: failure }], else_: null };
  }
  if (ts.isExpressionStatement(node)) {
    const e = skipParentheses(node.expression);
    if (ts.isBinaryExpression(e) && e.operatorToken.kind === ts.SyntaxKind.EqualsToken &&
        ts.isObjectLiteralExpression(skipParentheses(e.left)))
      return gate.objectAssignment(node, e);
    return {
      k: "effect",
      pos: gate.span(node),
      e: gate.expr(node.expression),
    };
  }

  if (ts.isReturnStatement(node)) {
    const start = node.getStart(gate.file);
    const keyword: Span = [start, start + "return".length];
    // A bare `return` returns `undefined`: the literal, at the keyword. In
    // an async body it settles the call's promise as completing does:
    // `return %AsyncComplete%()`.
    if (!node.expression)
      return {
        k: "return",
        pos: gate.span(node),
        e: gate.asyncBody
          ? gate.intrinsic(asyncCompleteName, gate.span(node), keyword, [])
          : { k: "lit", pos: keyword, lit: { a: "undefined" } },
      };
    const e = gate.expr(node.expression);
    // In a guard, a Boolean by its form returns the Boolean its truth is
    // (`booleanReturn`), the literals at the keyword's first two code units.
    if (gate.guardBody && !gate.asyncBody && booleanForm(e)) return booleanReturn(gate.span(node), e, start);
    // In an async body, `return e` is `return %AsyncReturn%(e)`, the call
    // spanning the statement, the intrinsic read at the keyword.
    return {
      k: "return",
      pos: gate.span(node),
      e: gate.asyncBody
        ? gate.intrinsic(asyncReturnName, gate.span(node), keyword, [e])
        : e,
    };
  }

  if (ts.isVariableStatement(node)) return gate.declarations(node.declarationList, node);

  if (ts.isBreakStatement(node)) {
    // A labeled `break` goes to the end of the block its labeled statement
    // is lowered to (`controlStmt`), through any loop, `switch` or `finally`
    // between.
    if (node.label) {
      const named = labeledTarget(node);
      if (!named) return gate.fail(node, "a break to a label no enclosing statement of the function has");
      return { k: "break", pos: gate.span(node), label: statementLabel(named, gate.file) };
    }
    const target = jumpTarget(node);
    if (!target)
      gate.fail(node, "break or continue outside a supported loop");
    // A `break` out of a `switch` goes to the end of the block it is
    // lowered to (`switchStmt`).
    return { k: "break", pos: gate.span(node),
      label: ts.isSwitchStatement(target) ? switchLabel(target, gate.file) : null };
  }
  if (ts.isContinueStatement(node)) {
    const target = continueTarget(node);
    if (!target)
      return gate.fail(node, node.label ? "a continue to a label no enclosing loop of the function has"
        : "break or continue outside a supported loop");
    // A `continue` of a loop with a binding per iteration leaves the block
    // its body runs in (`forStmt`); one of a loop whose body runs in a block
    // a `continue` leaves (`continueBlock`: a `do...while`, or a loop a
    // labeled `continue` repeats from a nested loop) leaves that block.
    if (ts.isForStatement(target) && capturesLoopLet(target))
      return { k: "break", pos: gate.span(node), label: iterationLabel(target, gate.file) };
    if (continueBlock(target))
      return { k: "break", pos: gate.span(node), label: continueLabel(target, gate.file) };
    if (jumpTarget(node) !== target)
      return gate.fail(node, "internal: a continue of an outer loop without the block it leaves");
    return { k: "continue", pos: gate.span(node) };
  }
  return gate.controlStmt(node);
}

/** The statement `({ k₁: t₁ = d₁, … } = e);`, `assignment` its expression:
 *
 *     { const %r = e;
 *       const { k₁: %h₁ = d₁ } = %r;  t₁ = %h₁;
 *       … }
 *
 * the right side once, then, property by property in source order, the
 * property's read, its default where the read is `undefined`, and the
 * write of its target, as JavaScript's destructuring assignment runs them;
 * a target that is itself an object pattern is assigned from `%hᵢ` the same
 * way. A target is a local the assignment writes (`assign`, which checks
 * its slot or cell). The first read throws on `null` and `undefined`
 * before any write, as RequireObjectCoercible does. The value of the
 * assignment is discarded: only a statement is lowered so. The names `%r`
 * and `%hᵢ` no source spells; the added statements' entries and claims are
 * the statement's free offsets (`sites`), the read of each property claimed
 * at its target's span. */
export function objectAssignment(this: Gate, node: ts.ExpressionStatement, assignment: ts.BinaryExpression): Within<{ value: "any"; store: "grow" }, Stmt> {
  const gate: Gate = this;
  const site = gate.sites(node);
  const entry = (): Span => {
    const o = site.entry();
    return [o, o + 1];
  };
  const tag = node.getStart(gate.file);
  let fresh = 0;
  const id = (name: string): Expr => ({ k: "id", pos: site.span(), name });
  const body: Stmt[] = [];
  const assigned = new Set<string>();
  const assign = (pattern: ts.ObjectLiteralExpression, source: string): void => {
    if (pattern.properties.length === 0)
      gate.fail(pattern, "an empty object pattern in an assignment assigns nothing");
    for (const p of pattern.properties) {
      let key: ts.Identifier, target: Node, dflt: ts.Expression | undefined;
      if (ts.isShorthandPropertyAssignment(p)) {
        const name = p.name;
        if (!ts.isIdentifier(name)) return gate.fail(name, "internal: a shorthand property without its name");
        key = name;
        target = name;
        dflt = p.objectAssignmentInitializer;
      } else if (ts.isPropertyAssignment(p)) {
        const name = p.name;
        if (!ts.isIdentifier(name))
          return gate.fail(name, "a computed or string key in an assignment pattern is outside the fragment");
        key = name;
        const init = p.initializer;
        if (ts.isBinaryExpression(init) && init.operatorToken.kind === ts.SyntaxKind.EqualsToken) {
          target = init.left;
          dflt = init.right;
        } else target = init;
      } else if (ts.isSpreadAssignment(p)) {
        return gate.fail(p, "a rest in an object assignment pattern is outside the fragment");
      } else return gate.fail(p, "an object assignment pattern holds properties");
      target = skipParentheses(target);
      // A default naming an anonymous function or class names it after the
      // target (NamedEvaluation), which the hidden binding would not.
      if (dflt && (ts.isFunctionExpression(skipParentheses(dflt)) || ts.isArrowFunction(skipParentheses(dflt)) ||
          ts.isClassExpression(skipParentheses(dflt))))
        gate.fail(dflt, "an anonymous function or class as a default of an assignment pattern is outside the fragment: it is named after its target");
      const hidden = `%assigned@${tag}%${fresh++}`;
      body.push({ k: "destructure", pos: entry(), default_: null, init: id(source), target: {
        k: "object", pos: site.span(), rest: null,
        props: [{ field: key.text, target: { k: "name", name: hidden, pos: gate.span(target) },
          default_: dflt ? gate.expr(dflt) : null }],
      } });
      if (ts.isIdentifier(target)) {
        if (target.text === "undefined")
          gate.fail(target, "shadowing undefined is outside the fragment");
        const name = gate.local(target);
        if (assigned.has(name)) gate.fail(target, "duplicate pattern binding");
        assigned.add(name);
        body.push({ k: "effect", pos: entry(), e: { k: "assign", pos: site.span(), name,
          namePos: gate.span(target), rhs: id(hidden) } });
      } else if (ts.isObjectLiteralExpression(target)) assign(target, hidden);
      else gate.fail(target, "an object assignment pattern writes a local or an object pattern: a field target is outside the fragment");
    }
  };
  const value = `%assigned@${tag}%`;
  const first = entry();
  body.push({ k: "const", pos: first, bindings: [{ early: false, name: value, namePos: first, annot: null,
    init: gate.expr(assignment.right) }] });
  const pattern = skipParentheses(assignment.left);
  if (!ts.isObjectLiteralExpression(pattern)) return gate.fail(pattern, "internal: an object assignment without its pattern");
  assign(pattern, value);
  return { k: "block", pos: gate.span(node), label: null, body };
}

/** A `let` or `const` declaration list, the statement `at` spans: a
 * variable statement, or a `for` loop's initializer. */
export function declarations(this: Gate, list: ts.VariableDeclarationList, at: Node): Within<{ value: "any"; store: "grow" }, Stmt> {
  const gate: Gate = this;
  gate.lexicalList(list, at);
  if (list.declarations.length > 1 && list.declarations.some((d) => !ts.isIdentifier(d.name)))
    gate.fail(at, "a declaration list with a pattern among several declarators is outside the fragment here: each declarator is a statement of its own, which a function's or a closure's body has and a module's top level or a `for` initializer does not");
  return gate.declarationsOf(list, list.declarations, at, gate.span(at));
}

/** The declarator `d` of the list `list`, the statement `at` holds it, as
 * a declaration of its own at `pos`: a pattern's, or a binding's. */
export function declarator(this: Gate, list: ts.VariableDeclarationList, d: ts.VariableDeclaration, at: Statement, pos: Span): Within<{ value: "any"; store: "grow" }, Stmt[]> {
  const gate: Gate = this;
  if (ts.isIdentifier(d.name)) return [gate.declarationsOf(list, [d], at, pos)];
  const mutable = gate.mutableList(list, at);
  return (mutable ? gate.letPatternOf(d, pos) : null) ?? [gate.patternStmt(d, at, mutable, pos)];
}

/** Refuses `list`, the statement `at` holds it, unless it is a `let` or a
 * `const` list. */
export function lexicalList(this: Gate, list: ts.VariableDeclarationList, at: Node): Within<{ value: "any"; store: "grow" }, void> {
  const gate: Gate = this;
  // `var` is function-scoped and hoisted, so it is not this binding form.
  if (!(list.flags & ts.NodeFlags.Const) && !(list.flags & ts.NodeFlags.Let))
    gate.fail(at, "`var` is outside the fragment");
}

/** Whether the bindings of `list`, the statement `at` holds it, are cells:
 * a `let` or `const` list (`lexicalList`). */
export function mutableList(this: Gate, list: ts.VariableDeclarationList, at: Node): Within<{ value: "any"; store: "grow" }, boolean> {
  const gate: Gate = this;
  gate.lexicalList(list, at);
  // A `let` statement whose bindings are all initialized and nothing
  // assigns is a `const`: each binding holds its initial value throughout,
  // so reading it reads that value, as a `const`'s read does.
  // A module `let` stays one, a module cell, whatever writes it.
  // A module constant some write may add a key to is one too
  // (`keyAddedConstant`).
  const moduleLet = (!(list.flags & ts.NodeFlags.Const) || gate.moduleCellConstants.has(list)) &&
    ts.isVariableStatement(at) && !!at.parent && ts.isSourceFile(at.parent);
  return moduleLet || (!(list.flags & ts.NodeFlags.Const) && !(ts.isVariableStatement(at) && gate.neverAssigned(list)));
}

/** The declarators `ds` of `list`, the statement `at` holds them, as one
 * declaration at `pos`. */
export function declarationsOf(this: Gate, list: ts.VariableDeclarationList, ds: readonly ts.VariableDeclaration[], at: Node, pos: Span): Within<{ value: "any"; store: "grow" }, Stmt> {
  const gate: Gate = this;
  const mutable = gate.mutableList(list, at);
  const kindWord = mutable ? "let" : "const";
  const [only, ...others] = ds;
  if (only && !others.length && !ts.isIdentifier(only.name)) return gate.patternStmt(only, at, mutable, pos);
  // A declaration list binds its declarators left to right, each
  // initializer seeing the earlier bindings, under the statement's one
  // entry. Each declarator is gated on its own terms.
  const bindings: BindingAst[] = ds.map((d) => {
    if (d.name.kind !== ts.SyntaxKind.Identifier)
      gate.fail(d, "destructuring is outside the fragment");
    if (d.name.text === "undefined")
      gate.fail(d, "shadowing undefined is outside the fragment");
    // `let x: T;` binds `undefined` where it is declared: it is
    // `let x: T | undefined = undefined`, the cell's contract admitting
    // the value it starts with. A read of it before an assignment is
    // `undefined`, and a read after one is at `T` only where Lean proves
    // the cell's current contents are, as for any other cell. Without an
    // annotation there is no contract (TypeScript's evolving `any`).
    if (!d.initializer) {
      if (!mutable || !d.type)
        gate.fail(d, `a \`${kindWord}\` needs an initializer`);
      return {
        name: gate.local(d.name),
        namePos: gate.span(d.name),
        annot: gate.optionalTypeOf(d.type, d),
        init: { k: "lit", pos: gate.span(d), lit: { a: "undefined" } },
        early: gate.earlyDecls.has(d),
      };
    }
    // For `let`, the storage contract is what every later assignment is
    // checked against. Written, it is the annotation; unwritten, the
    // producer states one for the binding and the adapter checks that,
    // rather than this taking the initializer's type for the contract.
    // A binding its own initializer reads, as a function calling the
    // constant it initializes does (`const visit = (n) => … visit(…)`): the
    // lowering binds the name after its initializer, so the read would name
    // another binding or none.
    const self = gate.local(d.name);
    // The recursive visitor preserves array stores, including calls through itself.
    const reads = (n: Node): Within<{ value: "any"; store: "grow" }, Node | undefined> => {
      if (ts.isTypeNode(n)) return undefined;
      if (ts.isIdentifier(n) && gate.local(n) === self) {
        const parent = n.parent;
        const key = (ts.isPropertyAccessExpression(parent) && parent.name === n) ||
          ((ts.isPropertyAssignment(parent) || ts.isMethodDeclaration(parent) || ts.isPropertySignatureDeclaration(parent)) &&
            parent.name === n);
        if (!key) return n;
      }
      return n.forEachChild(reads);
    };
    // A function literal's body and defaults run only when it is called,
    // after the binding holds it: there the read is the closure's self entry
    // (SOURCE-ELABORATION.md, "Recursive constants").
    let literal: Node = d.initializer;
    while (ts.isParenthesizedExpression(literal)) literal = literal.expression;
    const read = ts.isArrowFunction(literal) || ts.isFunctionExpression(literal) ? undefined : reads(d.initializer);
    if (read)
      gate.fail(read, `a binding read in its own initializer is outside the fragment: ${self} is bound after its initializer runs`);
    const early = gate.earlyDecls.has(d);
    return {
      name: gate.local(d.name),
      namePos: gate.span(d.name),
      annot: d.type ? gate.typeOf(d.type)
        : early && list.flags & ts.NodeFlags.Let ? literalDeclaredType(d.initializer, gate.span(d.initializer)) : null,
      init: gate.expr(d.initializer),
      early,
    };
  });
  if (mutable) return { k: "let", pos, bindings };
  return { k: "const", pos, bindings };
}

/** TypeScript's declared type for a `let` that `e` initializes, where the
 * source writes `e` as a literal naming nothing, parenthesized or not: a
 * Boolean, number, string or bigint literal, a template with no
 * substitution, a number or bigint literal under `-`, or a number literal
 * under `+`. It is the literal's primitive type, `boolean`, `number`,
 * `string` or `bigint`; any other initializer, an enum member's read among
 * them, gives `null`. */
export function literalDeclaredType(e: Expression, span: Span): TypeTerm | null {
  while (ts.isParenthesizedExpression(e)) e = e.expression;
  const atom = (name: "boolean" | "number" | "string" | "bigint"): TypeTerm => ({ k: "atom", name, span });
  if (e.kind === ts.SyntaxKind.TrueKeyword || e.kind === ts.SyntaxKind.FalseKeyword) return atom("boolean");
  if (ts.isNumericLiteral(e)) return atom("number");
  if (ts.isBigIntLiteral(e)) return atom("bigint");
  if (ts.isStringLiteral(e) || ts.isNoSubstitutionTemplateLiteral(e)) return atom("string");
  if (ts.isPrefixUnaryExpression(e)) {
    if (ts.isNumericLiteral(e.operand) &&
        (e.operator === ts.SyntaxKind.MinusToken || e.operator === ts.SyntaxKind.PlusToken)) return atom("number");
    if (ts.isBigIntLiteral(e.operand) && e.operator === ts.SyntaxKind.MinusToken) return atom("bigint");
  }
  return null;
}

/** Whether a `let` list's bindings are all initialized and none is
 * written in the scope it binds them in: no assignment, compound or
 * logical assignment, update or destructuring assignment names one. A
 * write is found by the name the fragment gives the binding (`local`), so
 * a same-named binding elsewhere in that scope keeps the list a `let`. */
export function neverAssigned(this: Gate, list: ts.VariableDeclarationList, loopHead: boolean = false): Within<{ value: "any"; store: "grow" }, boolean> {
  const gate: Gate = this;
  const [first] = list.declarations;
  // A loop head's binding is bound by each iteration, not by an initializer.
  if (!first || (!loopHead && list.declarations.some((d) => !d.initializer))) return false;
  const names = new Set<string>();
  const bind = (n: ts.BindingName): void => {
    if (ts.isIdentifier(n)) names.add(gate.local(n));
    else for (const e of n.elements) if (!ts.isOmittedExpression(e) && e.name) bind(e.name);
  };
  for (const d of list.declarations) bind(d.name);
  return !writesName(gate, bindingScope(first), names);
}

/** Whether a write within `scope` names one of `names`, the names the
 * fragment gives bindings (`local`): an assignment, a compound or logical
 * assignment, an update, a destructuring assignment or a `for` head's
 * target. A same-named binding declared within the scope shadows and has a
 * name of its own (`renames`). */
function writesName(gate: Gate, scope: Node, names: Set<string>): Within<{ value: "any"; store: "grow" }, boolean> {
  const targets = (e: Node): boolean => {
    while (ts.isParenthesizedExpression(e)) e = e.expression;
    if (ts.isIdentifier(e)) return names.has(gate.local(e));
    if (ts.isArrayLiteralExpression(e)) return e.elements.some(targets);
    if (ts.isObjectLiteralExpression(e)) return e.properties.some((p) =>
      ts.isShorthandPropertyAssignment(p) ? ts.isIdentifier(p.name) && names.has(gate.local(p.name))
        : ts.isPropertyAssignment(p) ? targets(p.initializer)
        : ts.isSpreadAssignment(p) ? targets(p.expression) : false);
    if (ts.isSpreadElement(e)) return targets(e.expression);
    if (ts.isBinaryExpression(e) && e.operatorToken.kind === ts.SyntaxKind.EqualsToken) return targets(e.left);
    return false;
  };
  const writes = (n: Node): boolean => {
    if (ts.isBinaryExpression(n) && n.operatorToken.kind >= ts.SyntaxKind.FirstAssignment &&
        n.operatorToken.kind <= ts.SyntaxKind.LastAssignment && targets(n.left)) return true;
    if ((ts.isPrefixUnaryExpression(n) || ts.isPostfixUnaryExpression(n)) &&
        (n.operator === ts.SyntaxKind.PlusPlusToken || n.operator === ts.SyntaxKind.MinusMinusToken) &&
        targets(n.operand)) return true;
    if ((ts.isForOfStatement(n) || ts.isForInStatement(n)) && !ts.isVariableDeclarationList(n.initializer) &&
        targets(n.initializer)) return true;
    return !!n.forEachChild((c) => writes(c) || undefined);
  };
  return writes(scope);
}

/** A loop's body: its statement, in the block a `continue` of the loop
 * leaves where the loop has one (`continueBlock`), so that the `continue`
 * goes to what follows the body: the test of a `do...while`, the update of a
 * `for`, the next step of a `for...of`. */
export function loopBody(this: Gate, loop: Loop): Within<{ value: "any"; store: "grow" }, Stmt[]> {
  const gate: Gate = this;
  const body = gate.block(loop.statement);
  return continueBlock(loop)
    ? [{ k: "block", pos: gate.span(loop.statement), label: continueLabel(loop, gate.file), body }]
    : body;
}

/** Loops, branches, blocks, labeled statements, `switch`, `try` and
 * `throw`. */
export function controlStmt(this: Gate, node: Statement): Within<{ value: "any"; store: "grow" }, Stmt> {
  const gate: Gate = this;
  if (ts.isWhileStatement(node))
    return {
      k: "while",
      pos: gate.span(node),
      cond: gate.expr(node.expression),
      body: gate.loopBody(node),
      update: [],
    };

  // `do s while (c)` is `while (true) { ℓ: { s } if (c) {} else break; }`:
  // the body first, then the test, the body in a block a `continue` of the
  // loop leaves (`continueBlock`), so it goes to the test, and its scope,
  // which the test does not see. The loop's entry is the statement's, the
  // `true` the `o` of `do`, the test's entry and its `break`'s the first two
  // offsets of `while`.
  if (ts.isDoStatement(node)) {
    const start = node.getStart(gate.file);
    const keyword = gate.token(node.statement.end, "while", node);
    return {
      k: "while",
      pos: gate.span(node),
      cond: { k: "lit", pos: [start + 1, start + 2], lit: { a: "booleanlit", v: "true" } },
      body: [
        ...gate.loopBody(node),
        { k: "if", pos: [keyword, keyword + 1], cond: gate.expr(node.expression), then: [],
          else_: [{ k: "break", pos: [keyword + 1, keyword + 2], label: null }] },
      ],
      update: [],
    };
  }

  // `ℓ: s` is the block `ℓ: { s }`, which a `break ℓ` leaves; a
  // `continue ℓ` of a loop `s` leaves the loop's body (`loopBody`).
  if (ts.isLabeledStatement(node))
    return { k: "block", pos: gate.span(node), label: statementLabel(node, gate.file), body: gate.block(node.statement) };

  if (ts.isForStatement(node)) return gate.forStmt(node);
  if (ts.isForInStatement(node)) return gate.forInStmt(node);
  if (ts.isSwitchStatement(node)) return gate.switchStmt(node);
  if (ts.isTryStatement(node)) return gate.tryStmt(node);
  // `throw e`: `e`, then a throw of its value, which leaves the function
  // unless a `try` around it catches it.
  if (ts.isThrowStatement(node))
    return { k: "throw", pos: gate.span(node), e: gate.expr(node.expression) };

  // `{ … }`: its statements in a scope of their own.
  if (ts.isBlock(node))
    return { k: "block", pos: gate.span(node), label: null, body: gate.statements(node.statements) };

  // `for (const x of e) body`: one immutable binding per iteration. The
  // iterable is the argument of the iteration intrinsic that steps its
  // iterator (`intrinsics.mts`), picked by TypeScript's type of it:
  // `%Iterate%` for an array, and the one of a string, a `Set`, a `Map` or
  // a host collection iterator. Lean checks the call at its signature.
  if (ts.isForOfStatement(node)) {
    if (node.awaitModifier)
      gate.fail(node, "`for await` is outside the fragment");
    // A `let` nothing assigns is a `const`, as a statement's is: each
    // iteration binds it afresh, and nothing changes it after.
    const list = node.initializer;
    if (!ts.isVariableDeclarationList(list) || list.declarations.length !== 1 ||
        !(list.flags & ts.NodeFlags.Const || (list.flags & ts.NodeFlags.Let && gate.neverAssigned(list, true))))
      gate.fail(node, "a `for...of` loop declares one `const` binding, or a `let` nothing assigns");
    const d = list.declarations[0];
    if (d.type || d.initializer)
      gate.fail(d, "a `for...of` binding takes the element's type");
    // `for (const p of e) s` with `p` a pattern is `for (const %e of e) {
    // const p = %e; s }`: each iteration binds the element, then the
    // pattern reads it, before the body, as JavaScript binds the pattern
    // per iteration. The element is a name no source spells, and the
    // pattern is a `const` pattern statement's.
    if (ts.isObjectBindingPattern(d.name) || ts.isArrayBindingPattern(d.name)) {
      const iterate = gate.iterations.get(gate.span(node.expression).join(":")) ?? iterateName;
      if (iterate === "client-unclosable")
        gate.fail(node.expression, UNCLOSABLE);
      // Over a program's iterable, the protocol's steps, the pattern
      // destructuring each value first in the closing region.
      if (iterate === "client" || iterate === "client-method")
        return gate.protocolForOf(node, list, d.name, iterate === "client-method");
      const c = list.getStart(gate.file);
      const element = `%element@${c}`;
      const bind = gate.forOfPattern(d, d.name, element, gate.span(d), [c, c + "const".length]);
      return {
        k: "forOf",
        pos: gate.span(node),
        name: element,
        namePos: gate.span(d.name),
        iterate,
        iterable: gate.expr(node.expression),
        body: [bind, ...gate.loopBody(node)],
      };
    }
    if (!ts.isIdentifier(d.name))
      gate.fail(d, "destructuring is outside the fragment");
    if (d.name.text === "undefined")
      gate.fail(d, "shadowing undefined is outside the fragment");
    const iterate = gate.iterations.get(gate.span(node.expression).join(":")) ?? iterateName;
    if (iterate === "client-unclosable")
      gate.fail(node.expression, UNCLOSABLE);
    if (iterate === "client" || iterate === "client-method")
      return gate.protocolForOf(node, list, d.name, iterate === "client-method");
    return {
      k: "forOf",
      pos: gate.span(node),
      name: gate.local(d.name),
      namePos: gate.span(d.name),
      iterate,
      iterable: gate.expr(node.expression),
      body: gate.loopBody(node),
    };
  }

  // `else if (c) s` is `else { if (c) s }`: an unbraced arm is the one
  // statement its block would hold (`block`).
  if (ts.isIfStatement(node)) {
    return {
      k: "if",
      pos: gate.span(node),
      cond: gate.expr(node.expression),
      then: gate.block(node.thenStatement),
      else_: node.elseStatement ? gate.block(node.elseStatement) : null,
    };
  }

  if (ts.isClassDeclaration(node)) return gate.classStmt(node);

  gate.fail(
    node,
    `statement outside the fragment (${ts.SyntaxKind[node.kind]})`,
  );
}

/** A declaration's header as `functionDecl` reads it: its result, its
 * guard, its stated effect and its parameters' contracts. */
type FunctionHeader = { retType: TypeTerm; guard: Guard | null; stated: StatedEffect | null; parameterTypes: TypeTerm[] };

/** A declaration with overloads, its implementation `node`: one unit per
 * overload, each the implementation's code at that overload's parameter and
 * result types, its name the overload's (SOURCE-ELABORATION.md, "Module
 * functions"). The implementation's own signature is no caller's. Every
 * overload states the implementation's type parameters, as written, and as
 * many parameters, none a rest or `this`. */
export function overloadedDecl(this: Gate, node: FunctionDeclaration, overloads: readonly FunctionDeclaration[]): FunctionAst[] {
  const gate: Gate = this;
  const source = node.getSourceFile();
  const parametersText = (o: FunctionDeclaration): string =>
    (o.typeParameters ?? []).map(p => p.getText(source)).join(",");
  if (node.modifiers?.some(modifier => modifier.kind === ts.SyntaxKind.AsyncKeyword))
    gate.fail(node, "an async declaration with overloads is outside the fragment");
  for (const o of [...overloads, node]) {
    if (parametersText(o) !== parametersText(node))
      gate.fail(o, "an overload stating type parameters other than its implementation's is outside the fragment");
    if (o.parameters.length !== node.parameters.length)
      gate.fail(o, "an overload taking as many parameters as its implementation is in the fragment, no other");
    if (o.parameters.some(p => p.dotDotDotToken || (ts.isIdentifier(p.name) && p.name.text === "this")))
      gate.fail(o, "a rest or `this` parameter of an overloaded declaration is outside the fragment");
    if (o.type && ts.isTypePredicateNode(o.type))
      gate.fail(o.type, "a type predicate on an overloaded declaration is outside the fragment");
    if (gate.statedResult(o.type, o).stated)
      gate.fail(o.type ?? o, "a statement (`Within`) on an overloaded declaration is outside the fragment");
  }
  return overloads.map(o => gate.functionDecl(node, o));
}

export function functionDecl(this: Gate, node: FunctionDeclaration, signature: FunctionDeclaration = node): FunctionAst {
  const gate: Gate = this;
  if (!node.name) gate.fail(node, "anonymous function");
  if (!signature.name) gate.fail(signature, "anonymous function");
  if (node.name.text === "undefined")
    gate.fail(node, "shadowing undefined is outside the fragment");
  // `export default function f` exports f's own binding as `default`, which
  // no code of an imported module writes (`writesName`).
  if (node.modifiers?.some(modifier => modifier.kind !== ts.SyntaxKind.ExportKeyword &&
      modifier.kind !== ts.SyntaxKind.AsyncKeyword && modifier.kind !== ts.SyntaxKind.DefaultKeyword))
    gate.fail(
      node,
      "only the export, default and async modifiers are admitted on a source function",
    );
  if (node.asteriskToken)
    gate.fail(node, GENERATOR);
  const isAsync = !!node.modifiers?.some(modifier => modifier.kind === ts.SyntaxKind.AsyncKeyword);
  if (!node.body) gate.fail(node, "a function must have a body");
  const prologue = gate.useStrict(node.body.statements);
  if (
    prologue.strict &&
    node.parameters.some((p) => p.initializer || p.dotDotDotToken || !ts.isIdentifier(p.name))
  )
    gate.fail(node, '"use strict" beside non-simple parameters');
  const outerStrict = gate.strict;
  gate.strict = outerStrict || prologue.strict;
  // A declaration is the entry point, not a callable of the fragment: a
  // `this: T` parameter is one more input assumed at its annotation, like
  // every other parameter, and the body's `this` is that parameter.
  const head = node.parameters[0];
  const receiverParam =
    !!head && ts.isIdentifier(head.name) && head.name.text === "this";
  if (
    receiverParam &&
    (!head.type || head.questionToken || head.dotDotDotToken)
  )
    gate.fail(head, "a receiver needs a required type annotation");
  const outerReceiverMode = gate.receiverMode;
  const outerAsync = gate.asyncBody;
  const outerGuard = gate.guardBody;
  gate.receiverMode = receiverParam
    ? gate.strict
      ? "strict"
      : "sloppy"
    : null;
  const typeParams = gate.enterTypeParams(node.typeParameters, undefined, true);
  try {
    gate.asyncBody = isAsync;
    if (typeParams.some(p => p.resolution) && gate.statedResult(node.type, node).stated)
      gate.fail(node.type ?? node, "`Within` on a resolution-qualified declaration is outside the fragment: such a unit claims no footprint");
    // The header is the signature's: the declaration's own, or an
    // overload's (`overloadedDecl`).
    const { retType, guard, stated, parameterTypes } = gate.headerTypes((): FunctionHeader => {
      const guard = gate.guardOf(signature);
      const written = gate.statedResult(signature.type, signature);
      const retType = guard ? guardResult(guard) : gate.typeOf(written.result, signature);
      const parameterTypes: TypeTerm[] = signature.parameters.map((p): TypeTerm => p.dotDotDotToken ? gate.moduleRestType(p, signature)
        : p.questionToken || p.initializer ? gate.optionalTypeOf(p.type, p)
        : gate.typeOf(p.type, p));
      return { retType, guard, stated: written.stated, parameterTypes };
    });
    gate.guardBody = guard !== null;
    // A parameter written as a pattern or with a default binds a hidden
    // name, which the caller's argument initializes; a `destructure` over
    // it, first in the body in parameter order, binds the source's names,
    // the default replacing an undefined argument. JavaScript evaluates
    // them there too, in order, before the body. Where the function writes
    // one of the names, they are cells (`parameterBinding`).
    const names = new Set<string>();
    const bindings: Stmt[] = [];
    // Each hidden name's pattern and default, as the source writes them.
    const bound = new Map<string, [PatternAst, Expr | null]>();
    const params = node.parameters.map((p, i): FunctionParamAst => {
      if (ts.isIdentifier(p.name) && p.name.text === "undefined")
        gate.fail(p, "shadowing undefined is outside the fragment");
      if (
        !p.questionToken &&
        !p.initializer &&
        !p.dotDotDotToken &&
        node.parameters.indexOf(p) > firstOptional(node.parameters)
      )
        gate.fail(p, "a required parameter cannot follow an optional one");
      if (p.dotDotDotToken) {
        if (p.questionToken) gate.fail(p, "a rest parameter is not optional");
        if (p !== node.parameters[node.parameters.length - 1])
          gate.fail(p, "a rest parameter must be the last one");
        if (!ts.isIdentifier(p.name))
          gate.fail(p, "a rest parameter pattern is outside the fragment");
      }
      if (ts.isIdentifier(p.name) && !p.initializer) {
        names.add(p.name.text);
        return {
          name: gate.local(p.name),
          pos: gate.span(p.name),
          type: parameterTypes[i] ?? gate.fail(p, "missing parameter contract"),
          ...(p.dotDotDotToken ? { rest: true as const } : {}),
        };
      }
      const hidden = parameterName(i);
      const at = gate.span(p.name);
      const target = gate.pattern(p.name, names);
      const default_ = p.initializer ? gate.expr(p.initializer) : null;
      bound.set(hidden, [target, default_]);
      // A written parameter is a cell at its annotation, or at the type its
      // literal default states (`literalDefaultName`).
      bindings.push(...gate.parameterBinding(p, node, gate.span(p), target, default_, hidden,
        ts.isIdentifier(p.name) && (p.type || literalDefaultName(p)) ? gate.typeOf(p.type, p) : null));
      return {
        name: hidden,
        pos: at,
        // A caller may pass `undefined` where there is a default.
        type: parameterTypes[i] ?? gate.fail(p, "missing parameter contract"),
      };
    });
    gate.initializedBefore(node, params.map((p): [PatternAst, Expr | null] =>
      bound.get(p.name) ?? [{ k: "name", name: p.name, pos: p.pos }, null]));
    // The written precondition (`@requires`), at the call's positions: the
    // receiver at 0 where a `this` parameter names it, each other parameter
    // at its place after it. An async declaration and one whose parameters
    // are not plain names state none: their callers establish nothing it
    // could assume. An exported one's callers outside the analyzed sources
    // are trusted to meet it (DESIGN.md, trust surface).
    const clauses = requiresTags(gate.file.text.slice(node.pos, node.getStart(gate.file)));
    let requires: IndexFact[] = [];
    if (clauses.length > 0) {
      if (isAsync) gate.fail(node, "a precondition (`@requires`) on an async function");
      if (node.parameters.some(p => p.dotDotDotToken || p.initializer || p.questionToken || !ts.isIdentifier(p.name)))
        gate.fail(node, "a precondition (`@requires`) on a function whose parameters are not plain required names");
      const elaborated = writtenPrecondition(gate, clauses, node.parameters.map((p, i) => ({
        name: ts.isIdentifier(p.name) ? p.name.text : "", type: parameterTypes[i] })), !!receiverParam);
      if (typeof elaborated === "string") gate.fail(node, elaborated);
      else requires = elaborated;
    }
    const body = [...bindings,
      ...this.statements(node.body.statements.filter((s) => !prologue.skip.has(s)))];
    return {
      name: node.name.text,
      namePos: gate.span(signature.name),
      typeParams,
      params,
      retType,
      guard,
      stated,
      requires,
      completion: isAsync ? "async" : "sync",
      body: isAsync ? gate.asyncCompletion(node.body, body) : body,
      strict: gate.strict,
    };
  } finally {
    gate.leaveTypeParams();
    gate.strict = outerStrict;
    gate.receiverMode = outerReceiverMode;
    gate.asyncBody = outerAsync;
    gate.guardBody = outerGuard;
  }
}

/** A written precondition's clauses elaborated to index facts at the call's
 * positions (`elaborateRequires`), over parameters named in order, a leading
 * `this` the receiver at 0 where `receiver` holds and each other parameter at
 * its place after it; each path's kind read through its declared type
 * (`fieldType`). A function's own module and a module importing it read its
 * clause through this one elaboration. The refusal's message where it is
 * refused. */
export function writtenPrecondition(gate: Gate, clauses: readonly string[],
    parameters: readonly { name: string; type: TypeTerm | undefined }[], receiver: boolean): Within<{ value: "any"; store: "grow" }, IndexFact[] | string> {
  const named = parameters.map(({ name, type }, i): ClauseParameter => ({
    name,
    position: receiver ? i : i + 1,
    at: (path) => {
      const t = type === undefined ? null : path.reduce<TypeTerm | null>((t, f) => t && fieldType(gate, t, f), type);
      return t === null ? null : t.k === "array" ? "array" : namesView(t) ? "view" : "other";
    },
  }));
  const elaborated = elaborateRequires(clauses, named);
  if ("refused" in elaborated) return `a precondition (\`@requires\`): ${elaborated.refused}`;
  if (!receiver && elaborated.facts.some(f => indexFactPositions(f).includes(0)))
    return "a precondition (`@requires`) names the receiver, which the function does not declare";
  return elaborated.facts;
}

/** The type of the required data field `f` of a value of type `t`, where a
 * record shape states one (`recordShape`): of a record type, an alias
 * followed to its equation, or the one part of an intersection that states
 * it; null where none does. A clause's path reads such fields alone. */
function fieldType(gate: Gate, t: TypeTerm, f: string, depth: number = 0): TypeTerm | null {
  const records = gate.namedRecords();
  if (records === null || depth > 16) return null;
  const refused = (): never => { throw new UnresolvedField(); };
  try {
    if (t.k === "object") {
      const field = t.fields.find(x => x.name === f);
      return field !== undefined && !field.optional ? field.type : null;
    }
    if (t.k === "intersection") {
      const found = t.parts.flatMap(p => { const r = fieldType(gate, p, f, depth + 1); return r === null ? [] : [r]; });
      return found.length === 1 ? found[0] ?? null : null;
    }
    if (t.k === "reference") {
      if (records.record(t.reference.target)) return fieldType(gate, recordShape(t, records, refused), f, depth + 1);
      const meaning = aliasMeaning(t, records, refused);
      return meaning === "record" ? null : fieldType(gate, meaning, f, depth + 1);
    }
  } catch (e) {
    if (e instanceof UnresolvedField) return null;
    throw e;
  }
  return null;
}

class UnresolvedField extends Error {}
