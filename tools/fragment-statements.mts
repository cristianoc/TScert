/* Part of the trusted front end (fragment-parse.mts): Patterns and statements: destructuring, iteration protocols, loops, `switch`, `try` and declarations.
 * Each function is a method of the gate: `Gate` holds it as a field, so a call
 * reads `this.name(...)`; its body names the gate `gate`, typed, which lets a
 * call that never returns (`gate.fail`) narrow what follows. */
import * as ts from "typescript/unstable/ast";
import type { Expression, FunctionDeclaration, Node, Statement } from "typescript/unstable/ast";
import type { BindingAst, Expr, FunctionAst, PatternAst, PatternElemAst, PatternPropAst, Stmt } from "./fragment.mts";
import type { Span } from "./span.mts";
import { assertionFailureName, asyncCompleteName, asyncReturnName, forInName, iterateForInName, iterateName } from "./intrinsics.mts";
import { GENERATOR, UNCLOSABLE, booleanForm, booleanReturn, bindingScope, firstOptional, forInEntryReads, freeOffsets, jumpTarget, namesRead, parameterName, patternNames, skipParentheses, switchLabel } from "./fragment-support.mts";
import type { Gate } from "./fragment-parse.mts";
import { guardResult } from "./fragment-guards.mts";

export function patternStmt(this: Gate, list: ts.VariableDeclarationList, node: Node, mutable: boolean): Stmt {
  const gate: Gate = this;
  if (mutable)
    gate.fail(node, "a `let` pattern whose bindings are assigned in a `for` head is outside the fragment: its bindings are cells, which only a statement of a block lowers them to (one never assigned is a `const` pattern)");
  if (list.declarations.length !== 1)
    gate.fail(node, "a pattern declares alone in the fragment");
  const d = list.declarations[0];
  if (d.type) gate.fail(d, "an annotated pattern is outside the fragment");
  if (!d.initializer) gate.fail(d, "a `const` needs an initializer");
  const kind = gate.iterations.get(gate.span(d.initializer).join(":"));
  if (ts.isArrayBindingPattern(d.name) && kind?.startsWith("client")) {
    if (kind === "client-unclosable" && !d.name.elements.some((e) => ts.isBindingElement(e) && e.dotDotDotToken))
      gate.fail(d.initializer, UNCLOSABLE);
    return gate.protocolPattern(d.name, d.initializer, node, kind === "client-method");
  }
  const target = gate.pattern(d.name, new Set(), ts.isArrayLiteralExpression(skipParentheses(d.initializer)));
  gate.initializedBefore(d, [[target, null]]);
  return {
    k: "destructure",
    pos: gate.span(node),
    target,
    default_: null,
    init: gate.expr(d.initializer),
  };
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
export function protocolPattern(this: Gate, pattern: ts.ArrayBindingPattern, init: Expression, node: Node, method: boolean): Stmt {
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
    statements.push({ k: "let", pos: [e, e + 1], bindings: named.map(({ cell }) => {
      const at = site.span();
      return { early: false, name: cell, namePos: at, annot: null, init: { k: "lit", pos: at, lit: { a: "undefined" } } };
    }) });
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
  statements.push({ k: "block", pos: gate.span(node), label, body: inner });
  gate.hoisted.push(...statements);
  const bindings: BindingAst[] = named.map(({ cell, name }) => ({ early: false, name: gate.local(name),
    namePos: gate.span(name), annot: null, init: { k: "id", pos: gate.span(name), name: cell } }));
  if (restName && restName.name && ts.isIdentifier(restName.name))
    bindings.push({ early: false, name: gate.local(restName.name), namePos: gate.span(restName.name), annot: null,
      init: { k: "id", pos: gate.span(restName.name), name: restCell } });
  return { k: "const", pos: gate.span(node), bindings };
}

/** One step of a collecting loop: the step, its `done` leaving by `leave`,
 * and the value pushed onto the fresh array `items`. */
export function collectStep(this: Gate, next: string, result: string, items: string, leave: () => Stmt,
    site: { entry(): number; span(): Span }): Stmt[] {
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
export function closeStatements(this: Gate, iteratorAt: () => Expr, tag: string, site: { entry(): number; span(): Span },
    method: boolean): Stmt[] {
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
export function collect(this: Gate, operand: Expression): Expr {
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
export function hoistTarget(this: Gate, s: Statement): ts.SpreadElement | null {
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
  const assigned = gate.assignedNames();
  // A name read before the spread runs after the collection: it must hold
  // the same value then, and its read must not throw where the source's
  // would (`readCannotThrow`).
  const initialized = (id: ts.Identifier): boolean => gate.readCannotThrow(id);
  const stable = (x: Node) => ts.isIdentifier(x) ? !assigned.has(x.text) && initialized(x)
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

/** Whether reading the name `id` cannot throw nor run code, and gives the
 * value it gives at any other read where the file assigns it nowhere: a
 * parameter, a function declaration with a body, a function body's `let` or
 * `const` the early-binding analysis finds initialized at every read
 * (`markEarly`), or a name the file declares nowhere that TypeScript binds
 * to the standard library's `var`s or functions alone (`libraryValues`); a
 * module binding, an import, a class, an ambient or unresolved name is not
 * one. */
export function readCannotThrow(this: Gate, id: ts.Identifier): boolean {
  const gate: Gate = this;
  for (let at: Node | undefined = id.parent; at; at = at.parent) {
    if (functionLikeNode(at) && at.parameters.some(p => ts.isIdentifier(p.name) && p.name.text === id.text))
      return true;
    const statements = ts.isBlock(at) || ts.isSourceFile(at) || ts.isCaseClause(at) || ts.isDefaultClause(at)
      ? at.statements : null;
    if (!statements) continue;
    for (const st of statements) {
      // A function declaration with a body is created when its scope is
      // entered; an ambient one (`declare function`, an overload without
      // a body) says nothing of what the name holds at run time.
      if (ts.isFunctionDeclaration(st) && st.name?.text === id.text) {
        const named = statements.filter((d): d is ts.FunctionDeclaration =>
          ts.isFunctionDeclaration(d) && d.name?.text === id.text);
        return named.some(d => !!d.body) &&
          !named.some(d => d.modifiers?.some(m => m.kind === ts.SyntaxKind.DeclareKeyword));
      }
      if (ts.isClassDeclaration(st) && st.name?.text === id.text) return false;
      if (ts.isImportDeclaration(st) && importedNames(st).includes(id.text)) return false;
      if (ts.isVariableStatement(st))
        for (const d of st.declarationList.declarations)
          if (ts.isIdentifier(d.name) && d.name.text === id.text)
            return !ts.isSourceFile(at) && !gate.earlyDecls.has(d);
    }
  }
  return gate.libraryValues.has(gate.span(id).join(":"));
}

/** The local names an import declaration binds. */
const importedNames = (st: ts.ImportDeclaration): string[] => {
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

/** The names the file assigns anywhere: an assignment, a compound or
 * logical one, an update, a destructuring assignment. */
export function assignedNames(this: Gate): Set<string> {
  const gate: Gate = this;
  if (gate.assigned) return gate.assigned;
  const names = new Set<string>();
  const targets = (e: Node): void => {
    while (ts.isParenthesizedExpression(e)) e = e.expression;
    if (ts.isIdentifier(e)) names.add(e.text);
    else if (ts.isArrayLiteralExpression(e)) e.elements.forEach(targets);
    else if (ts.isObjectLiteralExpression(e)) e.properties.forEach((p) =>
      ts.isShorthandPropertyAssignment(p) ? (ts.isIdentifier(p.name) ? names.add(p.name.text) : undefined)
        : ts.isPropertyAssignment(p) ? targets(p.initializer)
        : ts.isSpreadAssignment(p) ? targets(p.expression) : undefined);
    else if (ts.isSpreadElement(e)) targets(e.expression);
    else if (ts.isBinaryExpression(e) && e.operatorToken.kind === ts.SyntaxKind.EqualsToken) targets(e.left);
  };
  const visit = (n: Node): void => {
    if (ts.isBinaryExpression(n) && n.operatorToken.kind >= ts.SyntaxKind.FirstAssignment &&
        n.operatorToken.kind <= ts.SyntaxKind.LastAssignment) targets(n.left);
    if ((ts.isPrefixUnaryExpression(n) || ts.isPostfixUnaryExpression(n)) &&
        (n.operator === ts.SyntaxKind.PlusPlusToken || n.operator === ts.SyntaxKind.MinusMinusToken))
      targets(n.operand);
    if ((ts.isForOfStatement(n) || ts.isForInStatement(n)) && !ts.isVariableDeclarationList(n.initializer))
      targets(n.initializer);
    n.forEachChild(visit);
  };
  visit(gate.file);
  gate.assigned = names;
  return names;
}

export function initializedBefore(this: Gate, at: Node, targets: [PatternAst, Expr | null][]): void {
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

export function inert(this: Gate, e: Node): boolean {
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

export function patternDefaults(this: Gate, node: ts.BindingName): Node[] {
  const gate: Gate = this;
  if (ts.isIdentifier(node)) return [];
  return node.elements.flatMap((el): Node[] => ts.isOmittedExpression(el) ? []
    : [...(el.initializer ? [el.initializer] : []), ...(el.name ? gate.patternDefaults(el.name) : [])]);
}

export function steppedPattern(this: Gate, fresh: boolean,
    elements: { node: Node; hole: boolean; before: Node[]; after: Node[] }[]): void {
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
    { node: Node; hole: boolean; before: Node[]; after: Node[] }[] {
  return left.elements.map((el) => {
    if (ts.isOmittedExpression(el)) return { node: el, hole: true, before: [], after: [] };
    const assigned = ts.isBinaryExpression(el) && el.operatorToken.kind === ts.SyntaxKind.EqualsToken;
    const target = ts.isSpreadElement(el) ? el.expression : assigned ? el.left : el;
    const before = ts.isPropertyAccessExpression(target) ? [target.expression]
      : ts.isElementAccessExpression(target) ? [target.expression, target.argumentExpression] : [];
    const write = ts.isElementAccessExpression(target) ||
      ts.isPropertyAccessExpression(target) && ts.isIdentifier(target.name) && target.name.text === "length"
      ? [target] : [];
    return { node: el, hole: false, before, after: [...(assigned ? [el.right] : []), ...write] };
  });
}

export function pattern(this: Gate, node: ts.BindingName, names: Set<string>, fresh: boolean = false): PatternAst {
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
  // properties onto a fresh object (DESIGN.md, "Object literals").
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

export function block(this: Gate, node: Statement): Stmt[] {
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
 * changes no binding the live statements see: a `var` or function
 * declaration there is hoisted, and a `let`, `const` or `class` there binds
 * its name in the whole block, so a live reference to it would be to that
 * binding, forever uninitialized. */
export function statements(this: Gate, list: readonly Statement[]): Stmt[] {
  const gate: Gate = this;
  const end = list.findIndex((s) => gate.abrupt(s));
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
  for (const s of list.slice(live.length)) {
    if (typeStatement(s)) continue;
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
  for (const s of live) {
    const at = lexical.size ? refers(s) : undefined;
    if (at) gate.fail(at, "a name declared only in dead code is outside the fragment");
  }
  gate.markEarly(live);
  // An empty statement, `;`, does nothing; nor does a type declaration.
  return live.filter((s) => !ts.isEmptyStatement(s) && !typeStatement(s)).flatMap((s) => gate.hoisting(s));
}

/** A `type` or `interface` statement: TypeScript erases it, so it runs
 * nothing, wherever it is; it binds a type name over its block, which the
 * type readers resolve as TypeScript does (SOURCE-CONTRACTS.md,
 * "Block-scoped type declarations"). */
function typeStatement(s: Statement): boolean {
  return ts.isTypeAliasDeclaration(s) || ts.isInterfaceDeclaration(s);
}

/** The early bindings of a statement list (SOURCE-MODEL.md, "Lexical
 * bindings before initialization"): a one-name `let` or `const` of the list
 * one of whose mentions may run before the binding's initialization point,
 * the end of its declarator: a mention written before it, or one in a
 * closure created before it, which may run at any time after its creation.
 * A closure created after the point runs after it, in the same activation.
 * A function literal that is a constant's whole initializer runs only after
 * the constant holds it, so its mentions of the constant are the closure's
 * self entry. A pattern's binding so mentioned is refused. */
export function markEarly(this: Gate, live: readonly Statement[]): void {
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
  if (!declared.size && !patterns.size) return;
  // `created` is where the outermost closure around a mention is created,
  // null outside one: a closure created after a binding's initialization
  // point runs after it, in the same activation.
  const visit = (n: Node, created: number | null): void => {
    if (ts.isTypeNode(n)) return;
    if (ts.isIdentifier(n)) {
      const parent = n.parent;
      const key = !!parent && (((ts.isPropertyAccessExpression(parent) && parent.name === n) ||
        ((ts.isPropertyAssignment(parent) || ts.isMethodDeclaration(parent) ||
          ts.isPropertySignatureDeclaration(parent)) && parent.name === n)));
      const name = key ? undefined : gate.local(n);
      const at = created ?? n.getStart(gate.file);
      const d = name === undefined ? undefined : declared.get(name);
      if (d && n !== d.name && at < d.end) {
        let literal: Node | undefined = d.initializer;
        while (literal && ts.isParenthesizedExpression(literal)) literal = literal.expression;
        const self = !!literal && (ts.isArrowFunction(literal) || ts.isFunctionExpression(literal)) &&
          n.getStart(gate.file) >= literal.getStart(gate.file) && n.end <= literal.end;
        if (!self) gate.earlyDecls.add(d);
      }
      const p = name === undefined ? undefined : patterns.get(name);
      if (p && at < p.end && !(n.getStart(gate.file) >= p.name.getStart(gate.file) && n.end <= p.name.end))
        gate.fail(n, `a binding of a pattern read where it may be uninitialized is outside the fragment: ${n.text}`);
      return;
    }
    // A function declaration is created when its scope is entered (hoisted).
    const inner = created ?? (ts.isFunctionDeclaration(n) ? -1 : functionLike(n) ? n.getStart(gate.file) : null);
    n.forEachChild((c) => visit(c, inner));
  };
  for (const st of live) visit(st, null);
}

/** A statement, preceded by the statements its lowering runs before it:
 * the collection of a spread of a program's iterable (`collect`), or the
 * steps of an array pattern over one (`protocolPattern`). */
export function hoisting(this: Gate, s: Statement): Stmt[] {
  const gate: Gate = this;
  const savedHoist = gate.hoist, savedHoisted = gate.hoisted;
  let site: { entry(): number; span(): Span } | null = null;
  const lazy = () => site ??= gate.sites(s);
  gate.hoist = { stmt: s, spread: gate.hoistTarget(s),
    site: { entry: () => lazy().entry(), span: () => lazy().span() } };
  gate.hoisted = [];
  try {
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
export function letPattern(this: Gate, s: ts.VariableStatement): Stmt[] | null {
  const gate: Gate = this;
  const list = s.declarationList;
  const [d] = list.declarations;
  if (list.flags & ts.NodeFlags.Const || !(list.flags & ts.NodeFlags.Let) || list.declarations.length !== 1 ||
      !d || !(ts.isObjectBindingPattern(d.name) || ts.isArrayBindingPattern(d.name)) || gate.neverAssigned(list))
    return null;
  if (d.type) gate.fail(d, "an annotated pattern is outside the fragment");
  if (!d.initializer) gate.fail(d, "a `let` pattern needs an initializer");
  // Over a program's iterable, an array pattern is the iterator's steps
  // (`protocolPattern`), which bind no cells.
  if (ts.isArrayBindingPattern(d.name) &&
      gate.iterations.get(gate.span(d.initializer).join(":"))?.startsWith("client"))
    return null;
  const target = gate.pattern(d.name, new Set(), ts.isArrayLiteralExpression(skipParentheses(d.initializer)));
  gate.initializedBefore(d, [[target, null]]);
  const cells: BindingAst[] = [];
  const hide = (t: PatternAst): PatternAst => {
    switch (t.k) {
      case "name": {
        const hidden = `%let-pattern ${t.name}`;
        cells.push({ early: false, name: t.name, namePos: t.pos, annot: null, init: { k: "id", pos: t.pos, name: hidden } });
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
    { k: "destructure", pos: gate.span(s), target: hidden, default_: null, init: gate.expr(d.initializer) },
    { k: "let", pos: gate.span(d.name), bindings: cells },
  ];
}

/** The offset of `token` at or after `from`, past whitespace and comments:
 * a punctuator or keyword of `at` the tree has no node for. */
export function token(this: Gate, from: number, token: string, at: Node): number {
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
 * closure capturing it, which is refused. */
export function forStmt(this: Gate, node: ts.ForStatement): Stmt {
  const gate: Gate = this;
  const open = gate.token(node.getStart(gate.file) + "for".length, "(", node);
  const init = node.initializer;
  const first = gate.token(init ? init.end : open + 1, ";", node);
  const second = gate.token(node.condition ? node.condition.end : first + 1, ";", node);
  let initial: Stmt | null = null;
  if (init && ts.isVariableDeclarationList(init)) {
    if (init.flags & ts.NodeFlags.Let) {
      const names = new Set<string>();
      const collect = (n: Node): void => {
        if (ts.isIdentifier(n)) names.add(n.text);
        else n.forEachChild(collect);
      };
      for (const d of init.declarations) collect(d.name);
      const refers = (n: Node): Node | undefined =>
        ts.isIdentifier(n) && names.has(n.text) ? n : n.forEachChild(refers);
      const captures = (n: Node): Node | undefined =>
        ts.isFunctionLikeDeclaration(n) || ts.isClassLikeDeclaration(n) ? refers(n) : n.forEachChild(captures);
      for (const part of [node.condition, node.incrementor, node.statement]) {
        const at = part && captures(part);
        if (at) gate.fail(at, "a closure capturing a `for` loop's `let` binding is outside the fragment");
      }
    }
    initial = gate.declarations(init, init);
  } else if (init && ts.isExpression(init)) initial = { k: "effect", pos: gate.span(init), e: gate.expr(init) };
  else if (init) gate.fail(init, "a `for` initializer is a declaration or an expression");
  const loop: Stmt = {
    k: "while",
    pos: init ? [first, node.end] : gate.span(node),
    cond: node.condition
      ? gate.expr(node.condition)
      : { k: "lit", pos: [second, second + 1], lit: { a: "booleanlit", v: "true" } },
    body: gate.block(node.statement),
    update: node.incrementor
      ? [{ k: "effect", pos: gate.span(node.incrementor), e: gate.expr(node.incrementor) }]
      : [],
  };
  return initial ? { k: "block", pos: gate.span(node), label: null, body: [initial, loop] } : loop;
}

/** `for (const k in o) body` is `for (const k of %ForIn%(o)) body`: the
 * keys the loop visits, a string each (`intrinsics.mts`), the call at the
 * declaration, the intrinsic read at `in`. */
export function forInStmt(this: Gate, node: ts.ForInStatement): Stmt {
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
    body: gate.block(node.statement),
  };
}

/** The destructuring of a pattern binding a `for...of`, `const p = %element`,
 * which each iteration runs first, before the body: a `const` pattern
 * statement's over a value another reference may hold (an array's loop
 * reads its element in place, and a program's iterator may keep what it
 * yields), at the entry `pos`, its read of the element at `at`. */
export function forOfPattern(this: Gate, d: ts.VariableDeclaration, name: ts.BindingPattern, element: string,
    pos: Span, at: Span): Stmt {
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
    name: ts.BindingName, method: boolean): Stmt {
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
  // The close's sites: the header's runs of tokens the steps do not use.
  const entries = [o, o + 1, q];
  const spans: Span[] = [[n0, e1], [s, end], [e0, q + 1], [o, q + 1], [c, q + 1], [p, e1]];
  const close = gate.closeStatements(iteratorAt, `${s}`, {
    entry: () => entries.shift() ?? gate.fail(node, "internal: the close's entries"),
    span: () => spans.shift() ?? gate.fail(node, "internal: the close's sites"),
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
    { k: "closing", pos: [s + 1, s + 2], close, body: [...destructure, ...gate.block(node.statement)] },
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
 * from them are expression sites (`span`); none is a source node's site. */
export function sites(this: Gate, within: Node): { entry(): number; span(): Span } {
  const gate: Gate = this;
  const text = gate.file.text;
  let to = within.end;
  while (to < text.length && /\s/.test(text[to] ?? "")) to++;
  const free = freeOffsets(within, gate.file);
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
export function protocolStart(this: Gate, iterable: Expr, site: { entry(): number; span(): Span }, tag: string, at: Node):
    { bindings: BindingAst[]; iterator: string; next: string; iteratorAt: () => Expr } {
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
export function protocolStep(this: Gate, next: string, result: string, leave: () => Stmt,
    site: { entry(): number; span(): Span }): { stmts: Stmt[]; value: () => Expr } {
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
 * character), when every label is a literal or a name, since then nothing
 * between the tests writes and a field is a plain location; each test then
 * narrows the name, or the object's arms, as an `if` does. Any other is
 * evaluated first and bound to a name no source can spell. Every span is a node or a token: a test's `if`
 * begins at `case`, its read of the discriminant is at `case`, its `===`
 * at the clause's `:`, and its jump at the label; the jump to `default` is
 * at the keyword, the one to the switch's end at the clauses' `{`. The clauses
 * share one scope in JavaScript, so a name one declares directly must not
 * be read in another clause or in a label. */
export function switchStmt(this: Gate, node: ts.SwitchStatement): Stmt {
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
  const plain = (e: Expression): boolean => {
    const u = unwrap(e);
    return ts.isIdentifier(u) || ts.isStringLiteral(u) || ts.isNumericLiteral(u) ||
      u.kind === ts.SyntaxKind.TrueKeyword || u.kind === ts.SyntaxKind.FalseKeyword ||
      u.kind === ts.SyntaxKind.NullKeyword ||
      (ts.isPrefixUnaryExpression(u) && u.operator === ts.SyntaxKind.MinusToken && ts.isNumericLiteral(u.operand));
  };
  const discriminant = unwrap(node.expression);
  const bound: Stmt[] = [];
  let name: string;
  const fieldOf = ts.isPropertyAccessExpression(discriminant) && !discriminant.questionDotToken &&
    ts.isIdentifier(discriminant.expression) &&
    !gate.staticReads.has(gate.span(discriminant.name).join(":"))
    ? { object: gate.local(discriminant.expression), field: discriminant.name.text } : null;
  const reread = clauses.every((c) => !ts.isCaseClause(c) || plain(c.expression));
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
    dispatch.push({ k: "if", pos: [start, c.expression.end],
      cond: { k: "bin", pos: [colon, colon + 1], op: "===",
        l: fieldOf && reread
          ? { k: "read", pos: [start, start + "case".length], field: fieldOf.field,
              e: { k: "id", pos: [start, start + 1], name } }
          : { k: "id", pos: [start, start + "case".length], name },
        r: gate.expr(c.expression) },
      then: [{ k: "break", pos: gate.span(c.expression), label: label(c) }], else_: null });
  }
  const open = node.caseBlock.getStart(gate.file);
  dispatch.push(fallback ?? { k: "break", pos: [open, open + 1], label: end });
  const body = clauses.reduce<Stmt[]>((inner, c) =>
    [{ k: "block", pos: gate.span(c), label: label(c), body: inner }, ...this.statements(c.statements)], dispatch);
  return { k: "block", pos: gate.span(node), label: end, body: [...bound, ...body] };
}

/** `try { … } catch (e) { … } finally { … }`. The caught value is
 * `unknown`, the only annotation admitted: anything may be thrown. The
 * finalizer runs on every way out of the body and the handler, which the
 * lowering states by running it on each (`SourceExtraction`). */
export function tryStmt(this: Gate, node: ts.TryStatement): Stmt {
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
export function abrupt(this: Gate, s: Statement): boolean {
  const gate: Gate = this;
  return ts.isReturnStatement(s) || ts.isBreakStatement(s) || ts.isContinueStatement(s) ||
    ts.isThrowStatement(s) ||
    (ts.isBlock(s) && s.statements.some((t) => gate.abrupt(t))) ||
    (ts.isIfStatement(s) && !!s.elseStatement && gate.abrupt(s.thenStatement) && gate.abrupt(s.elseStatement)) ||
    // A `try` completes through its body or handler, then its `finally`.
    (ts.isTryStatement(s) && ((!!s.finallyBlock && gate.abrupt(s.finallyBlock)) ||
      (gate.abrupt(s.tryBlock) && (!s.catchClause || gate.abrupt(s.catchClause.block)))));
}

export function stmt(this: Gate, node: Statement): Stmt {
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
  if (ts.isExpressionStatement(node))
    return {
      k: "effect",
      pos: gate.span(node),
      e: gate.expr(node.expression),
    };

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

  if (ts.isBreakStatement(node) || ts.isContinueStatement(node)) {
    if (node.label)
      gate.fail(node, "only unlabeled loop transfers are supported");
    const target = jumpTarget(node);
    if (!target)
      gate.fail(node, "break or continue outside a supported loop");
    // A `break` out of a `switch` goes to the end of the block it is
    // lowered to (`switchStmt`).
    if (ts.isBreakStatement(node))
      return { k: "break", pos: gate.span(node),
        label: ts.isSwitchStatement(target) ? switchLabel(target, gate.file) : null };
    return { k: "continue", pos: gate.span(node) };
  }
  return gate.controlStmt(node);
}

/** A `let` or `const` declaration list, the statement `at` spans: a
 * variable statement, or a `for` loop's initializer. */
export function declarations(this: Gate, list: ts.VariableDeclarationList, at: Node): Stmt {
  const gate: Gate = this;
  // `var` is function-scoped and hoisted, so it is not this binding form.
  if (!(list.flags & ts.NodeFlags.Const) && !(list.flags & ts.NodeFlags.Let))
    gate.fail(at, "`var` is outside the fragment");
  // A `let` statement whose bindings are all initialized and nothing
  // assigns is a `const`: each binding holds its initial value throughout,
  // so reading it reads that value, as a `const`'s read does.
  // A module `let` stays one, a module cell, whatever writes it.
  const moduleLet = !(list.flags & ts.NodeFlags.Const) && ts.isVariableStatement(at) && !!at.parent && ts.isSourceFile(at.parent);
  const mutable = moduleLet || (!(list.flags & ts.NodeFlags.Const) && !(ts.isVariableStatement(at) && gate.neverAssigned(list)));
  const kindWord = mutable ? "let" : "const";
  if (
    list.declarations.some(
      (d) =>
        ts.isObjectBindingPattern(d.name) ||
        ts.isArrayBindingPattern(d.name),
    )
  )
    return gate.patternStmt(list, at, mutable);
  // A declaration list binds its declarators left to right, each
  // initializer seeing the earlier bindings, under the statement's one
  // entry. Each declarator is gated on its own terms.
  const bindings: BindingAst[] = list.declarations.map((d) => {
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
    const reads = (n: Node): Node | undefined => {
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
    // (SOURCE-MODEL.md, "Recursive constants").
    let literal: Node = d.initializer;
    while (ts.isParenthesizedExpression(literal)) literal = literal.expression;
    const read = ts.isArrowFunction(literal) || ts.isFunctionExpression(literal) ? undefined : reads(d.initializer);
    if (read)
      gate.fail(read, `a binding read in its own initializer is outside the fragment: ${self} is bound after its initializer runs`);
    return {
      name: gate.local(d.name),
      namePos: gate.span(d.name),
      annot: d.type ? gate.typeOf(d.type) : null,
      init: gate.expr(d.initializer),
      early: gate.earlyDecls.has(d),
    };
  });
  if (mutable) return { k: "let", pos: gate.span(at), bindings };
  return { k: "const", pos: gate.span(at), bindings };
}

/** Whether a `let` list's bindings are all initialized and none is
 * written in the scope it binds them in: no assignment, compound or
 * logical assignment, update or destructuring assignment names one. A
 * write is found by the name the fragment gives the binding (`local`), so
 * a same-named binding elsewhere in that scope keeps the list a `let`. */
export function neverAssigned(this: Gate, list: ts.VariableDeclarationList, loopHead: boolean = false): boolean {
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
  return !writes(bindingScope(first));
}

/** Loops, branches, blocks, `switch`, `try` and `throw`. */
export function controlStmt(this: Gate, node: Statement): Stmt {
  const gate: Gate = this;
  if (ts.isWhileStatement(node))
    return {
      k: "while",
      pos: gate.span(node),
      cond: gate.expr(node.expression),
      body: gate.block(node.statement),
      update: [],
    };

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
        body: [bind, ...gate.block(node.statement)],
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
      body: gate.block(node.statement),
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

  gate.fail(
    node,
    `statement outside the fragment (${ts.SyntaxKind[node.kind]})`,
  );
}

export function functionDecl(this: Gate, node: FunctionDeclaration): FunctionAst {
  const gate: Gate = this;
  if (!node.name) gate.fail(node, "anonymous function");
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
    const { retType, guard, parameterTypes } = gate.headerTypes(() => {
      const guard = gate.guardOf(node);
      return {
      retType: guard ? guardResult(guard) : gate.typeOf(node.type),
      guard,
      parameterTypes: node.parameters.map(p => p.dotDotDotToken ? gate.moduleRestType(p, node)
        : p.questionToken || p.initializer ? gate.optionalTypeOf(p.type, p)
        : gate.typeOf(p.type, p)),
      };
    });
    gate.guardBody = guard !== null;
    // A parameter written as a pattern or with a default binds a hidden
    // name, which the caller's argument initializes; a `destructure` over
    // it, first in the body in parameter order, binds the source's names,
    // the default replacing an undefined argument. JavaScript evaluates
    // them there too, in order, before the body.
    const names = new Set<string>();
    const bindings: Stmt[] = [];
    const params = node.parameters.map((p, i) => {
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
      bindings.push({
        k: "destructure",
        pos: gate.span(p),
        target: gate.pattern(p.name, names),
        default_: p.initializer ? gate.expr(p.initializer) : null,
        init: { k: "id", pos: at, name: hidden },
      });
      return {
        name: hidden,
        pos: at,
        // A caller may pass `undefined` where there is a default.
        type: parameterTypes[i] ?? gate.fail(p, "missing parameter contract"),
      };
    });
    gate.initializedBefore(node, params.map((p): [PatternAst, Expr | null] => {
      const b = bindings.find((st) => st.k === "destructure" && st.init.k === "id" && st.init.name === p.name);
      return b?.k === "destructure" ? [b.target, b.default_] : [{ k: "name", name: p.name, pos: p.pos }, null];
    }));
    const body = [...bindings,
      ...this.statements(node.body.statements.filter((s) => !prologue.skip.has(s)))];
    return {
      name: node.name.text,
      namePos: gate.span(node.name),
      typeParams,
      params,
      retType,
      guard,
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
