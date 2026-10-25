/* Part of the trusted front end (fragment-parse.mts): the syntax helpers and refusal
 * messages the gate's methods share. */
import * as ts from "typescript/unstable/ast";
import type { ClassDeclaration, Expression, FunctionDeclaration, Identifier, Node, SourceFile, TypeParameterDeclaration } from "typescript/unstable/ast";
import type { PropertyKey, TypeTerm } from "./declaration-types.mts";
import type { Expr, PatternAst, Stmt } from "./fragment.mts";
import type { Span } from "./span.mts";
import { isStatic, nameOf } from "./syntax.mts";
import { numberText } from "./intrinsics.mts";

/** A value typed `Promise<T>` is assumed to be a built-in promise, which is
 * never fulfilled with a thenable (SOURCE-CONTRACTS.md, "Async functions and await"):
 * so the source builds no object with a `then`, which could pass for one. */
/** A write at `Symbol.toStringTag`: no object the program makes holds the
 * tag the native `Promise` contract requires of its prototype
 * (SOURCE-CONTRACTS.md, "Async functions and await"). */
/** The standard library's `Symbol.toStringTag`, by its declaration identity. */
export const isTagSymbol = (s: { module: string; name: string }): boolean =>
  s.module === "typescript/lib/lib.es2015.symbol.wellknown.d.ts" && s.name === "toStringTag";
export const TAG_WRITE = "a write at `Symbol.toStringTag` is outside the fragment: no object the program makes holds the tag the native `Promise`, `Set` and `Map` contracts require";
/** An expression inside its parentheses. */
export const skipParentheses = (e: Node): Within<{ value: "any"; store: "grow" }, Node> => ts.isParenthesizedExpression(e) ? skipParentheses(e.expression) : e;

/** Why a generator is refused: its body stops at each `yield` and resumes
 * where it stopped when `next` is called again, and no term of the calculus
 * suspends in the middle of code. A generator is a state machine over its
 * suspension points, as TypeScript's downlevel emit writes it; that lowering
 * is not written. */
export const GENERATOR = "a generator function is outside the fragment: its body suspends at each `yield` and resumes there on the next call of `next`, which no term of the calculus expresses (the path is a state-machine lowering, as TypeScript's downlevel emit writes one)";

/** The offsets of a statement at which no node of it starts, that lie in no
 * function nested in it (whose statements have their own), from its start up
 * to the next token after it: where a lowering of the statement states the
 * entries of the statements it adds (`sites`), and where the claim reader
 * finds them. */
export function freeOffsets(within: Node, file: ts.SourceFile): Within<{ value: "any"; store: "grow" }, number[]> {
  const start = within.getStart(file);
  const text = file.text;
  let to = within.end;
  while (to < text.length && /\s/.test(text[to] ?? "")) to++;
  const starts = new Set<number>();
  const nested: Span[] = [];
  const visit = (n: Node): void => {
    starts.add(n.getStart(file));
    if (n !== within && (ts.isFunctionLikeDeclaration(n) || ts.isClassLikeDeclaration(n))) {
      nested.push([n.getStart(file), n.end]);
      return;
    }
    n.forEachChild(visit);
  };
  visit(within);
  const free: number[] = [];
  for (let o = start + 1; o < to; o++)
    if (!starts.has(o) && !nested.some(([a, b]) => a <= o && o < b)) free.push(o);
  return free;
}

/** A property key's JSON text: a string's JSON string, or `{"symbol":n}`
 * for the symbol of index `n`. It serializes only a string, so it calls no
 * `toJSON`. */
export function propertyKeyText(key: PropertyKey): Within<{ value: "keep"; store: "keep" }, string> {
  return typeof key === "string" ? JSON.stringify(key) : `{"symbol":${key.symbol}}`;
}

/** The span of an `if`'s closing parenthesis: the first character past its
 * condition that is neither white space nor a comment. */
export function conditionParen(node: ts.IfStatement, file: ts.SourceFile): Span {
  const text = file.text;
  let i = node.expression.end;
  for (;;) {
    if (/\s/.test(text[i] ?? "")) i++;
    else if (text.startsWith("//", i)) i = text.indexOf("\n", i) < 0 ? text.length : text.indexOf("\n", i);
    else if (text.startsWith("/*", i)) i = text.indexOf("*/", i) + 2;
    else break;
  }
  return [i, i + 1];
}

/** Why an iterable whose iterator's type states no `return` is refused where
 * the protocol may close it: leaving the loop early, or a throw out of its
 * body, calls the iterator's `return` if it has one, and an open record type
 * says nothing of that property, which may hold any function. */
export const UNCLOSABLE = "an iterable whose iterator's type states no `return` is outside the fragment here: a loop left early, or a throw out of its body, calls the iterator's `return` if it owns one (IteratorClose), and the iterator's open record type says nothing of what that property holds";
/** Why a spread of a program's iterable elsewhere is refused: collecting it
 * runs the iterator's code, which the lowering runs before the statement the
 * spread is in, and that is its place only where nothing the statement
 * evaluates before the spread can be changed by it. */
export const SPREAD_POSITION = "a spread of a program's iterable is outside the fragment here: its iterator's code runs where the spread is, which the lowering places before the statement, and that is its place only where the spread is the first evaluation of the statement's value able to run code, after literals and names that hold the same initialized value then";

/** A question-mark parameter requires an optional suffix. A default may
 * precede a required parameter: callers supply undefined in that position. */
/** The binding a class's static member is: a name no source binding can
 * spell, apart from the instance methods' `C.m`. */
export const staticName = (cls: string, member: string): Within<{ value: "any"; store: "grow" }, string> => `static ${cls}.${member}`;

/** Why an instance member reads none of its class's private static fields. */
export const INSTANCE_STATIC = "an instance member or constructor reading a private static field of its own class is outside the fragment: it is a binding the class defines after its methods and constructor, whose closures cannot hold it";
/** Why a static initializer reads its class only through its static fields. */
export const STATIC_INIT_CLASS = "a static initializer or static block reading its class other than through an earlier static field is outside the fragment: JavaScript runs it on a class value whose later static fields are undefined, where the model allocates the class value holding them after every initializer";
/** Why a closure a static initializer creates reads no static of its class. */
export const STATIC_INIT_CLOSURE = "a closure created by a static initializer or static block reading a static field of its class is outside the fragment: it may run after the field changes, and the class value does not exist yet where it is created";

/** Whether class `cls`, declared at the file's top level, declares a static
 * field named `name` by a property name: an own data property of its class
 * value. */
export function staticFieldOf(file: SourceFile, cls: string, name: string): Within<{ value: "any"; store: "grow" }, boolean> {
  return file.statements.some((s) => ts.isClassDeclaration(s) && s.name?.text === cls &&
    s.members.some((m) => ts.isPropertyDeclaration(m) && ts.isIdentifier(m.name) && m.name.text === name &&
      !!m.modifiers?.some((k) => k.kind === ts.SyntaxKind.StaticKeyword)));
}

/** Whether a node runs code of the program when evaluated: a call, a
 * construction, an iteration, a tagged template, an `await` or `yield`;
 * `except` names constructions that count as running none. A closure it
 * creates runs nothing until called. */
export function runsCode(node: Node, except: (n: ts.NewExpression) => Within<{ value: "any"; store: "grow" }, boolean> = () => false): Within<{ value: "any"; store: "grow" }, boolean> {
  const visit = (n: Node): boolean => {
    if (ts.isFunctionExpression(n) || ts.isArrowFunction(n) || ts.isFunctionDeclaration(n)) return false;
    if (ts.isNewExpression(n) && except(n)) return (n.arguments ?? []).some(visit);
    if (ts.isCallExpression(n) || ts.isNewExpression(n) || ts.isTaggedTemplateExpression(n) ||
        ts.isAwaitExpression(n) || ts.isYieldExpression(n) || ts.isForOfStatement(n) || ts.isSpreadElement(n) ||
        ts.isArrayBindingPattern(n) || ts.isTemplateExpression(n) || ts.isClassDeclaration(n) ||
        ts.isClassExpression(n)) return true;
    if (ts.isBinaryExpression(n) && n.operatorToken.kind === ts.SyntaxKind.InstanceOfKeyword) return true;
    return !!n.forEachChild((c) => visit(c) || undefined);
  };
  return visit(node);
}

/** Whether a class's static initializers may construct it before its class
 * value exists: constructing it runs no code (no base class, a constructor
 * and instance field initializers running none), and its static
 * initializers and blocks run none but those constructions, so no code of
 * the class, which reads the class value, runs before the class value is
 * bound. */
export function selfConstructs(declaration: ClassDeclaration): Within<{ value: "any"; store: "grow" }, boolean> {
  if (declaration.heritageClauses?.some((h) => h.token === ts.SyntaxKind.ExtendsKeyword)) return false;
  const cls = declaration.name?.text;
  const own = (n: ts.NewExpression) => ts.isIdentifier(n.expression) && n.expression.text === cls;
  // Constructing reads no static field either: one not yet initialized
  // holds nothing in JavaScript, which reads `undefined` there.
  const mentions = (n: Node): boolean => (ts.isIdentifier(n) && n.text === cls) ||
    !!n.forEachChild((c) => mentions(c) || undefined);
  return declaration.members.every((m) => {
    const isStaticMember = isStatic(m);
    if (ts.isConstructorDeclaration(m))
      return !m.parameters.some((p) => p.initializer && (runsCode(p.initializer) || mentions(p.initializer))) &&
        !(m.body && (runsCode(m.body) || mentions(m.body)));
    if (ts.isPropertyDeclaration(m))
      return !m.initializer || (isStaticMember ? !runsCode(m.initializer, own)
        : !runsCode(m.initializer) && !mentions(m.initializer));
    if (ts.isClassStaticBlockDeclaration(m)) return !runsCode(m.body, own);
    return true;
  });
}

/** The static method of class `cls`, declared at the file's top level, named
 * `name` (a property name or a private name's text). */
export function staticMethodOf(file: SourceFile, cls: string, name: string): Within<{ value: "any"; store: "grow" }, ts.MethodDeclaration | undefined> {
  for (const s of file.statements)
    if (ts.isClassDeclaration(s) && s.name?.text === cls)
      for (const m of s.members)
        if (ts.isMethodDeclaration(m) && (ts.isIdentifier(m.name) || ts.isPrivateIdentifier(m.name)) &&
            m.name.text === name && m.modifiers?.some((k) => k.kind === ts.SyntaxKind.StaticKeyword))
          return m;
  return undefined;
}


/** Why a class with a private name takes no part in inheritance. */
export const PRIVATE_INHERITANCE = "a class with a private name `#x` in inheritance is outside the fragment: a derived instance's base part is copied, and a copy holds no private slot";

/** The static member name of a class's `[Symbol.hasInstance]` method. */
export const HAS_INSTANCE = "[Symbol.hasInstance]";

/** The binding holding a class's prototype object: a name no source binding
 * can spell, apart from an instance method's `C.m` and a static member's. */
export const prototypeName = (cls: string): Within<{ value: "any"; store: "grow" }, string> => `${cls}.[[prototype]]`;

/** The key a class's prototype object owns and no other object does, which
 * `x instanceof C` looks for along `x`'s prototype chain: a name no source
 * key can spell (Lean's `Fragment.reservedSourceKey`). */
export const classKey = (cls: string): Within<{ value: "any"; store: "grow" }, string> => `[[${cls}.prototype]]`;

/** A class as a class extending it reads it: its constructor's parameters,
 * its methods (each the binding holding its closure, its base's included,
 * its own overriding them), and the binding holding its constructor at the
 * fresh instance it allocates. */
export type ClassRecord = { params: { name: string; type: TypeTerm }[]; methods: Map<string, string>; fresh: string;
  proto: string | null; binders: string[];
  /** The class is the standard `Error` itself (`native`), or extends it
   * through classes of the file (SOURCE-ELABORATION.md, a class extending
   * `Error`). */
  error?: "native" | "derived" };

/** The standard `Error` as a base: its construction takes one optional
 * message, a string; its prototype holds no method the file reads. */
export const errorBase = (span: Span): ClassRecord => ({ params: [{ name: "message",
  type: { k: "union", parts: [{ k: "atom", name: "string", span }, { k: "atom", name: "undefined", span }], span } }],
  methods: new Map(), fresh: "", proto: null, binders: [], error: "native" });

/** The binding holding an `Error`-derived instance's message. */
export const messageName = (cls: string): string => `${cls}.[[message]]`;

/** The binding holding the message argument `super` passes to `Error`. */
export const messageArgumentName = (cls: string): string => `${cls}.[[messageArgument]]`;

/** The binding holding a class's constructor where a class extends it: the
 * class value itself, claimed also at the fresh instance it allocates, whose
 * own keys are exactly known. */
export const freshName = (cls: string): Within<{ value: "any"; store: "grow" }, string> => `${cls}.[[class]]`;

/** The class's own binding of its name, which its instance methods, its
 * constructor and its instance field initializers read: JavaScript's class
 * scope binding, initialized before anything in the class body can run. A
 * name no source binding can spell; the initialization unit reads it as the
 * module value the class is (SOURCE-CONTRACTS.md, "Classes"). */
export const selfName = (cls: string): Within<{ value: "any"; store: "grow" }, string> => `${cls}.[[self]]`;

/** The binding holding a derived instance's base part. */
export const baseName = (cls: string): string => `${cls}.[[base]]`;

/** A part of an object literal: a named field, or a spread of a value. */
export type ObjectPart = { name: PropertyKey; e: Expr; computed?: true; spread?: never } | { spread: Expr; name?: never };

/** The hidden name a parameter written as a pattern or with a default
 * binds: a name no source binding can spell. The body's first statements
 * bind the source's names from it, in parameter order (`functionAst`). */
export const parameterName = (index: number): Within<{ value: "any"; store: "grow" }, string> => `parameter ${index}`;

/** Why a class member not named by a plain identifier is refused: each form
 * of name, by what it would mean. */
export function unnamedMember(member: ts.ClassElement, isStatic: boolean): string {
  const name = nameOf(member);
  if (name && ts.isPrivateIdentifier(name))
    return "a `#private` member is outside the fragment: it is a private slot of the instance, not a property, and the heap model has no such slot";
  if (name && ts.isComputedPropertyName(name)) {
    const key = name.expression;
    if (isStatic && ts.isPropertyAccessExpression(key) && ts.isIdentifier(key.expression) &&
        key.expression.text === "Symbol" && ts.isIdentifier(key.name) && key.name.text === "hasInstance")
      return "a static `[Symbol.hasInstance]` method is outside the fragment: it replaces the prototype-chain test that `instanceof` is in the model with a call";
    return isStatic
      ? "a static member with a computed key is outside the fragment: a static member is a binding named by its plain name"
      : "a class member with a computed key is outside the fragment: a method is a binding, and its prototype key, named by its plain name";
  }
  if (!name) return "a class member outside the fragment";
  return isStatic ? "a static member needs a plain name" : "a class member needs a plain name";
}

/** The names an expression reads, closures' included: a superset of what
 * it may read when it runs. */
export function namesRead(e: unknown, out: Set<string> = new Set()): Within<{ value: "any"; store: "grow" }, Set<string>> {
  if (Array.isArray(e)) e.forEach((x: unknown) => namesRead(x, out));
  else if (e !== null && typeof e === "object") {
    if ("k" in e && e.k === "id" && "name" in e && typeof e.name === "string") out.add(e.name);
    Object.values(e).forEach((v: unknown) => namesRead(v, out));
  }
  return out;
}

/** The names a pattern binds, in the order it binds them. */
export function patternNames(t: PatternAst): Within<{ value: "any"; store: "grow" }, string[]> {
  switch (t.k) {
    case "name": return [t.name];
    case "object": return [...t.props.flatMap((q) => patternNames(q.target)),
      ...(t.rest ? patternNames(t.rest.target) : [])];
    case "array": return [...t.elems.flatMap((q) => patternNames(q.target)),
      ...(t.rest ? patternNames(t.rest.target) : [])];
  }
}

/** The label of the block a `switch` is lowered to: a name no source can
 * spell. */
export const switchLabel = (node: ts.SwitchStatement, file: SourceFile): Within<{ value: "any"; store: "grow" }, string> => `%switch@${node.getStart(file)}%`;

/** The statement a `break` leaves or a `continue` repeats: the nearest
 * enclosing loop, or for a `break` also `switch`, not crossing into another
 * function. */
export function jumpTarget(node: ts.BreakStatement | ts.ContinueStatement): Within<{ value: "any"; store: "grow" }, Node | undefined> {
  for (let parent = node.parent; parent && !ts.isFunctionLikeDeclaration(parent); parent = parent.parent)
    if (ts.isWhileStatement(parent) || ts.isForStatement(parent) || ts.isForOfStatement(parent) ||
        ts.isForInStatement(parent) || (ts.isBreakStatement(node) && ts.isSwitchStatement(parent)))
      return parent;
  return undefined;
}

/** Whether a statement list can complete normally, rather than always
 * ending in a jump, a `return` or a `throw` (Lean's `abrupt`, negated). */
export function completes(ss: Stmt[]): Within<{ value: "any"; store: "grow" }, boolean> {
  const last = ss.at(-1);
  if (!last) return true;
  switch (last.k) {
    case "return": case "throw": case "break": case "continue": return false;
    case "if": return last.else_ === null || completes(last.then) || completes(last.else_);
    case "block": return last.label !== null || completes(last.body);
    case "try":
      if (last.finalizer !== null && !completes(last.finalizer)) return false;
      return completes(last.body) || (last.handler !== null && completes(last.handler.body));
    default: return true;
  }
}

export function firstOptional(
  parameters: readonly { questionToken?: unknown; initializer?: unknown }[],
): Within<{ value: "any"; store: "grow" }, number> {
  const i = parameters.findIndex((p) => !!p.questionToken);
  return i < 0 ? parameters.length : i;
}


/** A member of one of the file's enums: its name, its declaration's spans,
 * and its value as TypeScript computes it. */
export type EnumMember = { name: string; node: ts.EnumMember; span: Span; nameSpan: Span; init: Span | null;
  value: string | number | null };
/** An enum: where its declaration ends, whether it is ambient (`declare
 * enum`, not `const`), and its members, each value `undefined` until the
 * declaration graph reports it. */
export type EnumInfo = { end: number; ambient: boolean; members: EnumEntry[] };
/** An enum's member as the parser holds it: its value `undefined` until the
 * declaration graph reports it. */
export type EnumEntry = { name: string; node: ts.EnumMember; span: Span; nameSpan: Span; init: Span | null;
  value: string | number | undefined };

/** Whether an element access is written rather than read: the target of an
 * assignment, a compound assignment or an update, or `delete`'s operand. */
export function writtenElement(node: ts.ElementAccessExpression): Within<{ value: "any"; store: "grow" }, boolean> {
  let at: Node = node;
  while (at.parent && ts.isParenthesizedExpression(at.parent)) at = at.parent;
  const parent = at.parent;
  if (!parent) return false;
  if (ts.isBinaryExpression(parent) && parent.left === at &&
      parent.operatorToken.kind >= ts.SyntaxKind.FirstAssignment &&
      parent.operatorToken.kind <= ts.SyntaxKind.LastAssignment) return true;
  if ((ts.isPrefixUnaryExpression(parent) || ts.isPostfixUnaryExpression(parent)) &&
      (parent.operator === ts.SyntaxKind.PlusPlusToken || parent.operator === ts.SyntaxKind.MinusMinusToken))
    return true;
  return ts.isDeleteExpression(parent);
}

/** Whether a function's type parameter is named anywhere in it but at
 * `except`: its signature, its body, a nested function's (one declaring a
 * type parameter of the same name hides it there). */
export function typeParameterMentioned(node: FunctionDeclaration, parameter: TypeParameterDeclaration,
    except: Node): boolean {
  const name = parameter.name.text;
  const visit = (n: Node): boolean => {
    if (n === except || n === parameter) return false;
    if (n !== node && ts.isFunctionLikeDeclaration(n) &&
        n.typeParameters?.some((tp: TypeParameterDeclaration) => tp.name.text === name)) return false;
    if (ts.isTypeReferenceNode(n) && ts.isIdentifier(n.typeName) && n.typeName.text === name) return true;
    if (ts.isTypeQueryNode(n)) return false;
    return n.forEachChild(visit) ?? false;
  };
  return visit(node);
}

/** `Object.assign(arrow, literal)`: the callable form, a function with
 * properties. Its call, arrow and object literal, or null. */
export function callableAssign(node: Node): Within<{ value: "any"; store: "grow" }, CallableAssign | null> {
  if (!ts.isCallExpression(node) || !ts.isPropertyAccessExpression(node.expression) ||
      !ts.isIdentifier(node.expression.expression) || node.expression.expression.text !== "Object" ||
      node.expression.name.text !== "assign" || node.arguments.length !== 2)
    return null;
  const fn = node.arguments[0];
  const initial = node.arguments[1];
  return fn !== undefined && ts.isArrowFunction(fn) && initial !== undefined && ts.isObjectLiteralExpression(initial)
    ? { call: node, fn, initial } : null;
}

/** The nodes of `Object.assign(arrow, literal)` (`callableAssign`). */
export type CallableAssign = { call: ts.CallExpression; fn: ts.ArrowFunction; initial: ts.ObjectLiteralExpression };

/** The key of `k in o`, its parentheses dropped. */
export function inKey(node: ts.BinaryExpression): Within<{ value: "any"; store: "grow" }, Expression> {
  let key: Expression = node.left;
  while (ts.isParenthesizedExpression(key)) key = key.expression;
  return key;
}

/** The first identifier of `within` reading a value binding whose fragment
 * name (`local`) is in `names`. A type, and the name of a property, a
 * member, a destructured key, a label or a meta-property, reads no binding. */
export function readOf(within: Node, names: ReadonlySet<string>,
  local: (id: Identifier) => string): Within<{ value: "any"; store: "grow" }, Identifier | null> {
  const nameSlot = (id: Identifier): boolean => {
    const p = id.parent;
    if (!p) return false;
    if (ts.isPropertyAccessExpression(p) || ts.isPropertyAssignment(p) || ts.isMethodDeclaration(p) ||
        ts.isPropertyDeclaration(p) || ts.isGetAccessorDeclaration(p) || ts.isSetAccessorDeclaration(p) ||
        ts.isEnumMember(p)) return p.name === id;
    if (ts.isBindingElement(p)) return p.propertyName === id;
    return ts.isLabeledStatement(p) || ts.isBreakStatement(p) || ts.isContinueStatement(p) || ts.isMetaProperty(p);
  };
  const visit = (n: Node): Identifier | null => {
    if (ts.isTypeNode(n)) return null;
    if (ts.isIdentifier(n)) return !nameSlot(n) && names.has(local(n)) ? n : null;
    return n.forEachChild((c) => visit(c) ?? undefined) ?? null;
  };
  return visit(within);
}

/** Whether `within` writes a binding spelled `name`: an assignment, a
 * compound or logical one, an update, a destructuring assignment or a
 * `for...of`/`for...in` head naming it. By spelling, so a binding of
 * another scope with the same name counts too. */
export function writesName(within: Node, name: string): Within<{ value: "any"; store: "grow" }, boolean> {
  const targets = (e: Node): boolean => {
    while (ts.isParenthesizedExpression(e)) e = e.expression;
    if (ts.isIdentifier(e)) return e.text === name;
    if (ts.isArrayLiteralExpression(e)) return e.elements.some(targets);
    if (ts.isObjectLiteralExpression(e)) return e.properties.some((p) =>
      ts.isShorthandPropertyAssignment(p) ? ts.isIdentifier(p.name) && p.name.text === name
        : ts.isPropertyAssignment(p) ? targets(p.initializer)
        : ts.isSpreadAssignment(p) ? targets(p.expression) : false);
    if (ts.isSpreadElement(e)) return targets(e.expression);
    if (ts.isBinaryExpression(e) && e.operatorToken.kind === ts.SyntaxKind.EqualsToken) return targets(e.left);
    return false;
  };
  const visit = (n: Node): boolean => {
    if (ts.isBinaryExpression(n) && n.operatorToken.kind >= ts.SyntaxKind.FirstAssignment &&
        n.operatorToken.kind <= ts.SyntaxKind.LastAssignment && targets(n.left)) return true;
    if ((ts.isPrefixUnaryExpression(n) || ts.isPostfixUnaryExpression(n)) &&
        (n.operator === ts.SyntaxKind.PlusPlusToken || n.operator === ts.SyntaxKind.MinusMinusToken) &&
        targets(n.operand)) return true;
    if ((ts.isForOfStatement(n) || ts.isForInStatement(n)) && !ts.isVariableDeclarationList(n.initializer) &&
        targets(n.initializer)) return true;
    return !!n.forEachChild((c) => visit(c) || undefined);
  };
  return visit(within);
}

/** Whether running `node` may run code or write a property: a call, a
 * construction (a class's definition, whose static parts run, among them),
 * a tagged template, `await` or `yield` (other code runs meanwhile), an
 * iteration (a `for...of`, an array spread or pattern, which may step a
 * program's iterator), `instanceof` (which may call a static
 * `[Symbol.hasInstance]`), `delete`, a template (whose conversion of an
 * object calls its `toString`), or a write other than to a binding. A
 * function written there runs nothing until called, which is a call. The
 * implicit conversions of an object that run its code elsewhere (`o + ""`,
 * a relational comparison) are refused by the model (SOURCE-FRAGMENT.md, "Refused on
 * principle"), and a read runs none: an object holds data properties only. */
export function runsCodeOrWrites(node: Node): Within<{ value: "any"; store: "grow" }, boolean> {
  const target = (e: Node): Node => {
    while (ts.isParenthesizedExpression(e)) e = e.expression;
    return e;
  };
  const visit = (n: Node): boolean => {
    if (ts.isFunctionExpression(n) || ts.isArrowFunction(n) || ts.isFunctionDeclaration(n)) return false;
    if (ts.isCallExpression(n) || ts.isNewExpression(n) || ts.isTaggedTemplateExpression(n) ||
        ts.isAwaitExpression(n) || ts.isYieldExpression(n) || ts.isForOfStatement(n) || ts.isSpreadElement(n) ||
        ts.isArrayBindingPattern(n) || ts.isDeleteExpression(n) || ts.isTemplateExpression(n) ||
        ts.isClassDeclaration(n) || ts.isClassExpression(n)) return true;
    if (ts.isBinaryExpression(n) && (n.operatorToken.kind === ts.SyntaxKind.InstanceOfKeyword ||
        (n.operatorToken.kind >= ts.SyntaxKind.FirstAssignment &&
         n.operatorToken.kind <= ts.SyntaxKind.LastAssignment && !ts.isIdentifier(target(n.left))))) return true;
    if ((ts.isPrefixUnaryExpression(n) || ts.isPostfixUnaryExpression(n)) &&
        (n.operator === ts.SyntaxKind.PlusPlusToken || n.operator === ts.SyntaxKind.MinusMinusToken) &&
        !ts.isIdentifier(target(n.operand))) return true;
    return !!n.forEachChild((c) => visit(c) || undefined);
  };
  return visit(node);
}

/** The reads of the entry a `for...in` step visited, `P[k]` in
 * `for (const k in P) { … }` with `P` the loop's operand spelled again (a
 * name, or a chain of named reads from one) and `k` its key: each such read
 * in the statements the body starts with that run no code and write no
 * property (`runsCodeOrWrites`), outside the functions they define, and the
 * read that is the whole initializer, under a non-null assertion or not, of
 * the first declarator of the declaration that follows them. Each is the
 * entry the step visited, the value `P`'s object holds under `k` at the step:
 * nothing that ran since the step can change it, and `P` still denotes the
 * object the loop enumerates, since no code in the outermost function holding
 * the loop (the file, for a loop at the top level) writes `P`'s name and,
 * where `P` reads fields, running the loop's body runs no code and writes no
 * property, so no iteration changes what the chain finds. No declaration in
 * those statements, nor any of the body's own, spells the key's or `P`'s
 * name, which a read would then name instead. Empty where there is none. */
export function forInEntryReads(node: ts.ForInStatement): Within<{ value: "any"; store: "grow" }, ts.ElementAccessExpression[]> {
  const list = node.initializer;
  if (!ts.isVariableDeclarationList(list) || list.declarations.length !== 1) return [];
  const key = list.declarations[0]?.name;
  if (!key || !ts.isIdentifier(key) || !ts.isBlock(node.statement)) return [];
  const samePath = (a: Expression, b: Expression): Identifier | null =>
    ts.isIdentifier(a) && ts.isIdentifier(b) ? (a.text === b.text ? a : null)
    : ts.isPropertyAccessExpression(a) && ts.isPropertyAccessExpression(b) && !a.questionDotToken &&
      !b.questionDotToken && ts.isIdentifier(a.name) && ts.isIdentifier(b.name) && a.name.text === b.name.text
      ? samePath(a.expression, b.expression) : null;
  const rootOf = (e: Expression): Identifier | null => ts.isIdentifier(e) ? e
    : ts.isPropertyAccessExpression(e) && !e.questionDotToken && ts.isIdentifier(e.name) ? rootOf(e.expression) : null;
  const root = rootOf(node.expression);
  if (!root || root.text === key.text) return [];
  const names = new Set([key.text, root.text]);
  const entry = (e: Node): e is ts.ElementAccessExpression =>
    ts.isElementAccessExpression(e) && !e.questionDotToken && ts.isIdentifier(e.argumentExpression) &&
    e.argumentExpression.text === key.text && samePath(e.expression, node.expression) !== null;
  // A declaration spelling the key's or the root's name, outside the
  // functions a statement defines (whose bodies run later, if at all).
  const shadows = (n: Node): boolean => {
    if (ts.isFunctionExpression(n) || ts.isArrowFunction(n)) return false;
    if (ts.isFunctionDeclaration(n) || ts.isClassDeclaration(n)) return !!n.name && names.has(n.name.text);
    if ((ts.isVariableDeclaration(n) || ts.isBindingElement(n)) && n.name && ts.isIdentifier(n.name) &&
        names.has(n.name.text)) return true;
    return !!n.forEachChild((c) => shadows(c) || undefined);
  };
  // The body's own declarations bind from its start (a `let` or `const` in
  // its temporal dead zone until its declaration runs).
  for (const s of node.statement.statements)
    if ((ts.isVariableStatement(s) || ts.isFunctionDeclaration(s) || ts.isClassDeclaration(s)) && shadows(s)) return [];
  const reads: ts.ElementAccessExpression[] = [];
  const collect = (n: Node): void => {
    if (ts.isFunctionExpression(n) || ts.isArrowFunction(n) || ts.isFunctionDeclaration(n)) return;
    if (entry(n) && !writtenElement(n)) reads.push(n);
    n.forEachChild(collect);
  };
  for (const s of node.statement.statements) {
    if (!runsCodeOrWrites(s)) {
      if (shadows(s)) return [];
      collect(s);
      continue;
    }
    const declaration = ts.isVariableStatement(s) ? s.declarationList.declarations[0] : undefined;
    let read: Expression | undefined = declaration?.initializer;
    while (read && ts.isParenthesizedExpression(read)) read = read.expression;
    if (read && ts.isNonNullExpression(read)) read = read.expression;
    if (read && entry(read)) reads.push(read);
    break;
  }
  if (!reads.length) return [];
  // A binding declared in a function is written only there; one declared at
  // the top level, only at the top level or in a function, all in the file.
  let scope: Node | undefined;
  let file: Node = node;
  for (let at: Node | undefined = node.parent; at; at = at.parent) {
    if (ts.isFunctionLikeDeclaration(at)) scope = at;
    file = at;
  }
  if (writesName(scope ?? file, root.text)) return [];
  if (!ts.isIdentifier(node.expression) && runsCodeOrWrites(node.statement)) return [];
  return reads;
}

/** The module constant holding the value of member `member` of enum `name`
 * where that value is known only at run time (`enumStmt`). */
export const enumMemberName = (name: string, member: string): Within<{ value: "any"; store: "grow" }, string> => `%${name}.${member}%`;

/** An enum member's value as a literal expression. */
export function literalExpr(value: string | number, pos: Span): Within<{ value: "any"; store: "grow" }, Expr> {
  return typeof value === "string"
    ? { k: "lit", pos, lit: { a: "stringlit", v: value } }
    : { k: "lit", pos, lit: { a: "numberlit", v: numberText(value) } };
}

/* ------------------------------------------------------------- parsing -- */

/**
 * The whole file, or a gate rejection. A rejection is an Error whose message
 * begins "gate: ", which is what the command writes to stderr, so a caller and
 * the command report one wording.
 *
 * `carriesContext` is for a caller that assembled the file itself and put
 * declarations beside the function it is asking about — the coverage run does, so
 * that a function is typed with the names its own file declares rather than
 * failing for what extracting it left behind. Those declarations are then not
 * the subject: they are skipped rather than rejected, and nothing about them
 * is verified. A type they introduce still has to be sayable in a claim, so a
 * function that depends on one fails on that claim, in its own words.
 */
/** The name the fragment gives a local that shadows a binding of an
 * enclosing scope: its spelling and where it is declared, which no source
 * binding can spell. */
export function shadowName(id: Identifier, source: SourceFile): string {
  const { line, character } = source.getLineAndCharacterOfPosition(id.getStart(source));
  return `${id.text}@${line + 1}:${character + 1}`;
}

/** The scope a value declaration binds its name in, JavaScript's: a
 * parameter its function's, a `let`, `const`, class or function declaration
 * its block's (a `switch`'s clauses sharing one), a `for` head's binding the
 * loop's, a `var` its function's, a caught value its `catch` clause's, a
 * named function or class expression its own. */
export function bindingScope(node: Node): Within<{ value: "any"; store: "grow" }, Node> {
  const block = (n: Node): Node => (ts.isCaseClause(n) || ts.isDefaultClause(n)) && n.parent ? n.parent : n;
  const functionOf = (n: Node): Node => {
    let at: Node | undefined = n.parent;
    while (at && !ts.isFunctionLikeDeclaration(at) && !ts.isSourceFile(at)) at = at.parent;
    return at ?? n;
  };
  if (ts.isBindingElement(node)) {
    let at: Node | undefined = node.parent;
    while (at && !ts.isVariableDeclaration(at) && !ts.isParameterDeclaration(at)) at = at.parent;
    return at ? bindingScope(at) : node;
  }
  if (ts.isParameterDeclaration(node)) return node.parent ?? node;
  if (ts.isVariableDeclaration(node)) {
    const list = node.parent;
    if (!list || ts.isCatchClause(list)) return list ?? node;
    if (!(list.flags & (ts.NodeFlags.Let | ts.NodeFlags.Const))) return functionOf(node);
    const holder = list.parent;
    if (!holder) return list;
    if (ts.isForStatement(holder) || ts.isForOfStatement(holder) || ts.isForInStatement(holder)) return holder;
    return holder.parent ? block(holder.parent) : holder;
  }
  if (ts.isFunctionExpression(node) || ts.isClassExpression(node)) return node;
  return node.parent ? block(node.parent) : node;
}

/** The file's local value bindings that shadow a binding of an enclosing
 * scope, by the span of their name: a declaration whose name another
 * declaration binds in a scope enclosing its own (a named function or class
 * expression's own name encloses its parameters). */
export function shadowingLocals(source: SourceFile): Map<string, Identifier> {
  const declared: { id: Identifier; scope: Node; own: boolean }[] = [];
  const visit = (node: Node): void => {
    if (ts.isTypeNode(node) || ts.isInterfaceDeclaration(node) || ts.isTypeAliasDeclaration(node)) return;
    const name = nameOf(node);
    if ((ts.isParameterDeclaration(node) || ts.isVariableDeclaration(node) || ts.isBindingElement(node) ||
         ts.isFunctionDeclaration(node) || ts.isClassDeclaration(node) || ts.isEnumDeclaration(node) ||
         ts.isFunctionExpression(node) || ts.isClassExpression(node) || ts.isImportSpecifier(node) ||
         ts.isNamespaceImport(node) || ts.isImportClause(node)) &&
        name && ts.isIdentifier(name) && name.text !== "this")
      declared.push({ id: name, own: ts.isFunctionExpression(node) || ts.isClassExpression(node),
        scope: ts.isImportSpecifier(node) || ts.isNamespaceImport(node) || ts.isImportClause(node)
          ? source : bindingScope(node) });
    node.forEachChild(visit);
  };
  visit(source);
  const encloses = (outer: Node, inner: Node): boolean => {
    for (let at: Node | undefined = inner.parent; at; at = at.parent) if (at === outer) return true;
    return false;
  };
  const found = new Map<string, Identifier>();
  for (const d of declared)
    if (declared.some(o => o !== d && o.id.text === d.id.text &&
        (encloses(o.scope, d.scope) || (o.scope === d.scope && o.own && !d.own))))
      found.set(`${d.id.getStart(source)}:${d.id.end}`, d.id);
  return found;
}


/** Whether an expression's value is a Boolean by its form: a test of a
 * shape, a key, an instance or a family guard's tags, an equality, a
 * negation, a comparison, or `&&` and `||` of such. Its value is then its
 * truth. */
export function booleanForm(e: Expr): Within<{ value: "any"; store: "grow" }, boolean> {
  switch (e.k) {
    case "typeofTest": case "arrayTest": case "inTest": case "instanceTest": case "tagMember": case "not": return true;
    case "bin": return e.op === "===" || e.op === "!==" || e.op === "==" || e.op === "!=" ||
      ((e.op === "&&" || e.op === "||") && booleanForm(e.l) && booleanForm(e.r));
    case "arith": return e.op === "lt" || e.op === "le" || e.op === "gt" || e.op === "ge";
    default: return false;
  }
}

/** `return e` of a Boolean by its form, `if (e) return true; else return
 * false;`: a condition the lowering dispatches on, each answer refining what
 * it tests, as a guard's promise is checked at each return. The literals are
 * at the two code units from `at`, which no expression has (a `return`
 * keyword's, an arrow's `=>`), each the span of its own `return`. */
export function booleanReturn(pos: Span, e: Expr, at: number): Within<{ value: "any"; store: "grow" }, Stmt> {
  return {
    k: "if", pos, cond: e,
    then: [{ k: "return", pos: [at, at + 1], e: { k: "lit", pos: [at, at + 1], lit: { a: "booleanlit", v: "true" } } }],
    else_: [{ k: "return", pos: [at + 1, at + 2], e: { k: "lit", pos: [at + 1, at + 2], lit: { a: "booleanlit", v: "false" } } }],
  };
}
