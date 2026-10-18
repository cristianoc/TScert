#!/usr/bin/env node
/**
 * Everywhere the node side tells the compiler not to check something, or
 * leaves a unit's boundary unstated, found with the compiler the project
 * builds with. `tsc` has no option for these, and `typescript-eslint` cannot
 * check them here because it does not support TypeScript 7.
 *
 *   node tools/unchecked.mts [--list] [--project DIR --expect]
 *
 * The node side is every file `tools/tsconfig.json` includes. With
 * `--project`, the files another project's `tsconfig.json` includes; with
 * `--expect`, every report must fall on a line ending in the comment
 * `// expected: KIND` and every such line must be reported, which is how
 * `tests/unchecked-project/` holds the counterexamples each report exists
 * for.
 *
 * A written `any` is not a weaker type, it is the absence of one: the compiler
 * stops reading the expression, so a field that does not exist reads as
 * `undefined` rather than failing. That is not hypothetical here — two checks
 * on type-parameter defaults read `tp.default` through an `any` for as long as
 * they existed, and never once fired.
 *
 * A value the checker types `any` is the same absence, arriving from a
 * library (`JSON.parse`, a member a declaration file leaves untyped) or from
 * an array literal no annotation types (`let xs = []`). `[typed any]`:
 *
 * - an expression or a declaration whose value is `any` (itself, a member of
 *   a union or an intersection, or a type argument, at any depth) is reported
 *   unless the place it flows to reads it as `unknown`: its contextual type
 *   is `unknown` at each such `any`, or it is the operand of `typeof`, `!`,
 *   `void`, `throw`, an equality or a template, a condition, or an expression
 *   statement. A place typed `any` gives no such guarantee: a library
 *   function taking `any` may store it anywhere (`Object.assign`);
 * - an expression whose type holds `any` deeper, at a positive position (a
 *   property, an index signature's value, a signature's result, a parameter
 *   of a parameter), is reported where its contextual type differs there
 *   from its own and is not `unknown`, as `JSON.parse` bound at
 *   `(s: string) => number` is; and where it is an argument bound to a type
 *   parameter the call infers, which takes it whatever it holds;
 * - a member's receiver whose type holds `any` only inside it (`xs.map` of
 *   an `any[]`) is not itself reported: the member's type is, and so is what
 *   the member passes on, such as a callback's parameter, where it is
 *   declared;
 * - `new Map()` and `new Set()` of the standard library, constructed from
 *   nothing, take the type arguments of the place they flow to, where those
 *   hold no `any`;
 * - `JSON.parse(text)` of the standard library flows also into a place that
 *   takes every `Json` of calculus.mts, the parsed data the reviewed overlay
 *   of library globals states (`ParsedJson` in library-globals.mts).
 *
 * Each report names where the `any` arises; what it then flows into is not
 * reported again. A type whose inspection fails, because the compiler's API
 * does not return a part of it or the inspection exceeds its budget, is
 * reported as `[uninspected]`.
 *
 * A function without annotations leaves its boundary to inference.
 * `[unannotated]`: every function declaration; a class's methods, accessors
 * and constructor and every function its fields hold; an object literal's
 * methods, accessors and function-valued properties, unless a written type
 * gives the literal its contextual type; and every function a module binding
 * or `export default` holds (through parentheses, assertions, conditionals,
 * logical operators and array literals), unless a written type gives it its
 * contextual type. Each states the type of every parameter and, but for a
 * constructor or a setter, its result. What lies inside a unit is inferred
 * and checked there: a local `const` or `let`, and a function written as an
 * argument or held by a local.
 *
 * An `as` says the value is something the compiler cannot see that it is, and
 * a `!` says it is there when the compiler cannot see that either. Both are
 * assertions: nothing checks them, and a decoder that establishes the fact is
 * what they stand in for. `as const` and `as unknown` are not counted: they
 * assert nothing about a value, the first only asking for the literal type of
 * what is written there, the second widening to the type every value has.
 *
 * Each `as` and `!` written must carry its reason, a comment
 * `// asserted: REASON` at the end of its line or alone on the line above: a
 * decoder's last line, where the checks it just ran become the type it
 * returns, or an assertion whose check would cost more than it guards. An
 * `any`, written or computed, and a missing annotation have no reason that
 * excuses them: each is an error, as is an assertion without a reason, and
 * the command fails on one.
 */
import { spawn } from "node:child_process";
import fs from "node:fs";
import { availableParallelism } from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { API, SignatureKind, TypeFlags, isTypeReference, type Checker, type NodeHandle, type Program, type Type } from "typescript/unstable/sync";
import * as ts from "typescript/unstable/ast";
import type { Node, SourceFile } from "typescript/unstable/ast";
import { nameOf } from "./syntax.mts";

/** What was found, which report it is, and the reason written with it. */
type Kind = "any" | "as" | "!" | "typed any" | "unannotated" | "uninspected";
interface Found {
  file: string;
  line: number;
  column: number;
  kind: Kind;
  text: string;
  reason: string | null;
}

const KINDS: Kind[] = ["any", "typed any", "unannotated", "uninspected", "as", "!"];

/** The reports a written reason can carry. */
const REASONED: Kind[] = ["as", "!"];

/** `x as const` or `x as unknown`: an `as` asserting nothing. */
function assertsNothing(node: Node): boolean {
  if (!ts.isAsExpression(node)) return false;
  const type = node.type;
  return type.kind === ts.SyntaxKind.UnknownKeyword ||
    (ts.isTypeReferenceNode(type) && ts.isIdentifier(type.typeName) && type.typeName.text === "const");
}

const WRITTEN: [number, Kind][] = [
  [ts.SyntaxKind.AnyKeyword, "any"],
  [ts.SyntaxKind.AsExpression, "as"],
  [ts.SyntaxKind.NonNullExpression, "!"],
];

const REASON = /\/\/ asserted: (\S.*)$/;

/** The reason given for what is written on `line` (0-based) of `lines`: at
 * the end of that line, or as the whole of the line above. */
function reasonAt(lines: string[], line: number): string | null {
  const own = REASON.exec(lines[line] ?? "");
  if (own?.[1]) return own[1];
  const above = (lines[line - 1] ?? "").trim();
  const alone = above.startsWith("//") ? REASON.exec(above) : null;
  return alone?.[1] ?? null;
}

const LOGICAL: number[] = [
  ts.SyntaxKind.AmpersandAmpersandToken,
  ts.SyntaxKind.BarBarToken,
  ts.SyntaxKind.QuestionQuestionToken,
];

const EQUALITY: number[] = [
  ts.SyntaxKind.EqualsEqualsEqualsToken,
  ts.SyntaxKind.ExclamationEqualsEqualsToken,
  ts.SyntaxKind.EqualsEqualsToken,
  ts.SyntaxKind.ExclamationEqualsToken,
];

/* ------------------------------------------------------ the boundaries -- */

/** What a function-like declaration leaves unstated: each parameter without
 * a type, and its result where it has one to state. */
function unstated(node: ts.SignatureDeclaration, result: boolean): string[] {
  const missing = node.parameters
    .filter((parameter) => parameter.type === undefined)
    .map((parameter) => `parameter ${parameter.name.getText()}`);
  return result && node.type === undefined ? [...missing, "result"] : missing;
}

/** The functions a value holds as itself: through parentheses, assertions,
 * the branches of a conditional or a logical operator, and the elements of
 * an array literal. An object literal's members are checked as every object
 * literal's are; a function written as an argument is the call's. */
function heldFunctions(node: Node | undefined): (ts.ArrowFunction | ts.FunctionExpression)[] {
  if (node === undefined) return [];
  if (ts.isArrowFunction(node) || ts.isFunctionExpression(node)) return [node];
  if (ts.isParenthesizedExpression(node) || ts.isAsExpression(node) || ts.isSatisfiesExpression(node) ||
    ts.isNonNullExpression(node)) return heldFunctions(node.expression);
  if (ts.isConditionalExpression(node)) return [...heldFunctions(node.whenTrue), ...heldFunctions(node.whenFalse)];
  if (ts.isBinaryExpression(node) && LOGICAL.includes(node.operatorToken.kind))
    return [...heldFunctions(node.left), ...heldFunctions(node.right)];
  if (ts.isArrayLiteralExpression(node)) return node.elements.flatMap((element) => heldFunctions(element));
  return [];
}

/** Whether a written type gives `node` its contextual type: one exists and
 * is neither `any` nor a type parameter. */
function writtenContext(checker: Checker, node: Node): boolean {
  if (!ts.isExpression(node)) return false;
  const context = checker.getContextualType(node);
  return context !== undefined && !(context.flags & TypeFlags.Any) && !context.isTypeParameter();
}

/** The function-like nodes `node` puts at a unit's boundary, each with what
 * it leaves unstated. */
function boundary(checker: Checker, node: Node, moduleLevel: boolean): [Node, string[]][] {
  const parent = node.parent;
  const member = parent !== undefined &&
    (ts.isClassLikeDeclaration(parent) || (ts.isObjectLiteralExpression(parent) && !writtenContext(checker, parent)));
  if (ts.isFunctionDeclaration(node)) return [[node, unstated(node, true)]];
  if (ts.isConstructorDeclaration(node)) return [[node, unstated(node, false)]];
  if (member && (ts.isMethodDeclaration(node) || ts.isGetAccessorDeclaration(node))) return [[node, unstated(node, true)]];
  if (member && ts.isSetAccessorDeclaration(node)) return [[node, unstated(node, false)]];
  const held = (value: Node | undefined): [Node, string[]][] =>
    heldFunctions(value).filter((fn) => !writtenContext(checker, fn)).map((fn): [Node, string[]] => [fn, unstated(fn, true)]);
  if (member && (ts.isPropertyAssignment(node) || ts.isPropertyDeclaration(node))) return held(node.initializer);
  if (moduleLevel && ts.isVariableDeclaration(node)) return held(node.initializer);
  if (ts.isExportAssignment(node)) return held(node.expression);
  return [];
}

/* ------------------------------------------------------------ the types -- */

/** The checker's types, inspected for `any` once each. A type holds `any`
 * at a positive position: itself, a member of a union or an intersection, a
 * type argument, a property, an index signature's value, a signature's
 * result, and a parameter of a function at a parameter; a parameter's own
 * type is a negative position, where `any` is a value the type's user
 * supplies, and the members of a value supplied there are read by the code
 * it is supplied to. */
class Inspection {
  private readonly checker: Checker;
  private readonly holding: Map<string, boolean | null> = new Map<string, boolean | null>();
  private readonly values: Map<string, boolean | null> = new Map<string, boolean | null>();
  private readonly taking: Map<string, boolean | null> = new Map<string, boolean | null>();
  private readonly keys: Map<number, string> = new Map<number, string>();
  private readonly written: Map<string, Type | undefined | null> = new Map<string, Type | undefined | null>();
  /** Queries left before an inspection stops as exhausted. */
  private budget: number = 20_000_000;
  constructor(checker: Checker) {
    this.checker = checker;
  }

  /** A query to the compiler, `null` where it fails or the budget is spent. */
  private ask<T>(query: () => T): T | null {
    if (--this.budget < 0) return null;
    try {
      return query();
    } catch {
      return null;
    }
  }

  /** The positions of `type` one step down, each with whether its polarity
   * is the type's, or `null` where the compiler's API does not give them. */
  private positions(type: Type, positive: boolean): [Type, boolean][] | null {
    const checker = this.checker;
    if (type.isUnionType() || type.isIntersectionType()) {
      const parts = this.ask(() => type.getTypes() ?? []);
      return parts && parts.map((part): [Type, boolean] => [part, true]);
    }
    if (!type.isObjectType()) return [];
    const out: [Type, boolean][] = [];
    if (isTypeReference(type)) {
      const args = this.ask(() => checker.getTypeArguments(type));
      const target = this.declaredOf(type);
      if (!args || target === null) return null;
      for (const arg of args) out.push([arg, true]);
      // An instance's members are the generic type's at its arguments: the
      // generic type is inspected once for all of its instances. A tuple,
      // which no declaration names, is its arguments.
      if (target === undefined) return out;
      if (target.id !== type.id) return positive ? [...out, [target, true]] : out;
    }
    // An instance of a written type (a type literal, a function or mapped
    // type, a member's or a function's type) is that type at the arguments
    // of its alias and of the instances enclosing it: the written type is
    // inspected once for all of its instances.
    const written = this.writtenForm(type);
    if (written === null) return null;
    if (written && written.id !== type.id) {
      const aliasArgs = this.ask(() => type.getAliasTypeArguments());
      if (!aliasArgs) return null;
      return [...out, ...aliasArgs.map((arg): [Type, boolean] => [arg, true]), [written, true]];
    }
    // A value the code supplies is read by the code it is given to; only a
    // function it supplies is given values in return, at its parameters.
    if (!positive) return [...out, ...(this.signaturePositions(type) ?? [])];
    const properties = this.ask(() => checker.getPropertiesOfType(type));
    if (!properties) return null;
    const propertyTypes = properties.length ? this.ask(() => checker.getTypeOfSymbol(properties)) : [];
    if (!propertyTypes) return null;
    for (const property of propertyTypes) if (property) out.push([property, true]);
    const indexes = this.ask(() => checker.getIndexInfosOfType(type));
    if (!indexes) return null;
    for (const index of indexes) out.push([index.valueType, true]);
    const signatures = this.signaturePositions(type);
    return signatures && [...out, ...signatures];
  }

  /** A type's identity up to the copies the checker makes of a generic
   * signature's type parameters at each instance: a type parameter by its
   * declaration, a union, an intersection and a type reference by their
   * parts and arguments, anything else by its id. A generic member whose
   * result instantiates its own type again (`Promise.then`) yields a fresh
   * type at each instance; by this identity the family repeats, and a search
   * through it ends. */
  private canonical(type: Type, depth: number = 0): string {
    const known = this.keys.get(type.id);
    if (known !== undefined) return known;
    let key = `#${type.id}`;
    if (depth < 16) {
      if (type.isTypeParameter()) {
        const symbol = this.ask(() => type.getSymbol());
        if (symbol) key = `P${symbol.id}`;
      } else if (type.isUnionType() || type.isIntersectionType()) {
        const parts = this.ask(() => type.getTypes() ?? []);
        if (parts) key = `${type.isUnionType() ? "U" : "I"}(${parts.map((part) => this.canonical(part, depth + 1)).sort().join(",")})`;
      } else if (isTypeReference(type)) {
        const args = this.ask(() => this.checker.getTypeArguments(type));
        const target = this.ask(() => type.getTarget());
        if (args && target) key = `R${target.id}<${args.map((arg) => this.canonical(arg, depth + 1)).join(",")}>`;
      }
    }
    this.keys.set(type.id, key);
    return key;
  }

  /** The generic type a type reference instantiates, as its declaration
   * states it once: `undefined` for a reference no declaration names (a
   * tuple), `null` where the compiler's API fails. */
  private declaredOf(type: Type): Type | undefined | null {
    const symbol = this.ask(() => type.getSymbol());
    if (symbol === null) return null;
    if (!symbol) return undefined;
    const site = `declared ${symbol.id}`;
    const cached = this.written.get(site);
    if (cached !== undefined) return cached;
    const declared = this.ask(() => this.checker.getDeclaredTypeOfSymbol(symbol));
    const form = declared === null ? null : declared.isErrorType() ? undefined : declared;
    this.written.set(site, form);
    return form;
  }

  /** The type one declaration of `type` writes, uninstantiated: a type
   * node's, or a named member's or function's at its name; `undefined` where
   * no one declaration states it, `null` where the compiler's API fails. */
  private writtenForm(type: Type): Type | undefined | null {
    const declarations = this.ask(() => type.getSymbol()?.declarations ?? []);
    if (!declarations) return null;
    const [only] = declarations;
    if (declarations.length !== 1 || !only) return undefined;
    // One type per declaration: the compiler may answer each query with a
    // fresh instance, whose positions would be fresh in turn.
    const site = `${only.path}#${only.index}`;
    const cached = this.written.get(site);
    if (cached !== undefined) return cached;
    const form = this.readWritten(only);
    this.written.set(site, form);
    return form;
  }

  private readWritten(only: NodeHandle): Type | undefined | null {
    const node = this.ask(() => only.resolve());
    if (node === null) return null;
    if (!node) return undefined;
    const name = ts.isTypeNode(node) ? undefined : nameOf(node);
    if (!ts.isTypeNode(node) && !(name && ts.isIdentifier(name))) return undefined;
    const written = this.ask(() => ts.isTypeNode(node) ? this.checker.getTypeFromTypeNode(node)
      : name ? this.checker.getTypeAtLocation(name) : undefined);
    return written === null ? null : written ?? undefined;
  }

  /** The results and parameters of `type`'s call and construct signatures. */
  private signaturePositions(type: Type): [Type, boolean][] | null {
    const checker = this.checker;
    const out: [Type, boolean][] = [];
    for (const kind of [SignatureKind.Call, SignatureKind.Construct]) {
      const signatures = this.ask(() => checker.getSignaturesOfType(type, kind));
      if (!signatures) return null;
      for (const signature of signatures) {
        const result = this.ask(() => checker.getReturnTypeOfSignature(signature));
        if (result === null) return null;
        if (result) out.push([result, true]);
        const parameters = signature.getParameters();
        const parameterTypes = parameters.length ? this.ask(() => checker.getTypeOfSymbol(parameters)) : [];
        if (!parameterTypes) return null;
        for (const parameter of parameterTypes) if (parameter) out.push([parameter, false]);
      }
    }
    return out;
  }

  /** Whether an `any` at a positive position is reachable from `start`
   * along `step`; `null` where a step fails and none is reachable otherwise.
   * Every type is expanded once: the search decides each strongly connected
   * group of the types it meets together (Tarjan's algorithm, iteratively),
   * and records the answer of each. */
  private reach(start: [Type, boolean], step: (type: Type, positive: boolean) => [Type, boolean][] | null,
      memo: Map<string, boolean | null>): boolean | null {
    const key = ([type, positive]: [Type, boolean]): string => `${this.canonical(type)}:${positive}`;
    const first = memo.get(key(start));
    if (first !== undefined) return first;
    type Frame = { key: string; next: [Type, boolean][]; at: number; answer: boolean | null };
    const index = new Map<string, number>();
    const low = new Map<string, number>();
    const onStack = new Set<string>();
    const stack: string[] = [];
    const frames: Frame[] = [];
    const pending = new Map<string, boolean | null>();
    const combine = (a: boolean | null, b: boolean | null): boolean | null => (a || b ? true : a === null || b === null ? null : false);
    const enter = (node: [Type, boolean]): void => {
      const k = key(node);
      const [type, positive] = node;
      index.set(k, index.size);
      low.set(k, index.get(k) ?? 0);
      stack.push(k);
      onStack.add(k);
      const leaf = type.isErrorType() ? false : type.flags & TypeFlags.Any ? positive : undefined;
      const next = leaf === undefined ? step(type, positive) : [];
      frames.push({ key: k, next: (next ?? []).map(([inner, same]): [Type, boolean] => [inner, same === positive]),
        at: 0, answer: leaf ?? (next === null ? null : false) });
    };
    enter(start);
    let last: boolean | null = false;
    while (frames.length) {
      const frame = frames[frames.length - 1];
      if (!frame) break;
      const child = frame.next[frame.at];
      if (child) {
        frame.at++;
        const ck = key(child);
        const known = memo.get(ck);
        if (known !== undefined) frame.answer = combine(frame.answer, known);
        else if (!index.has(ck)) enter(child);
        else if (onStack.has(ck)) low.set(frame.key, Math.min(low.get(frame.key) ?? 0, index.get(ck) ?? 0));
        continue;
      }
      frames.pop();
      const parent = frames[frames.length - 1];
      if ((low.get(frame.key) ?? 0) === index.get(frame.key)) {
        // The root of a group: every member shares the group's answer.
        const members: string[] = [];
        for (let k = stack.pop(); k !== undefined; k = stack.pop()) {
          onStack.delete(k);
          members.push(k);
          if (k === frame.key) break;
        }
        let answer = frame.answer;
        for (const m of members) answer = combine(answer, pending.get(m) ?? false);
        for (const m of members) memo.set(m, answer);
        last = answer;
        if (parent) parent.answer = combine(parent.answer, answer);
      } else {
        pending.set(frame.key, frame.answer);
        if (parent) {
          low.set(parent.key, Math.min(low.get(parent.key) ?? 0, low.get(frame.key) ?? 0));
          parent.answer = combine(parent.answer, frame.answer);
        }
      }
    }
    return memo.get(key(start)) ?? last;
  }

  /** Whether `type` holds `any` at a position of the polarity `positive`;
   * `null` where the inspection cannot finish. */
  holds(type: Type, positive: boolean = true): boolean | null {
    return this.reach([type, positive], (inner, polarity) => this.positions(inner, polarity), this.holding);
  }

  /** Whether a value of `type` is `any`: the type itself, a member of a
   * union or an intersection, or a type argument, at any depth. */
  isAny(type: Type): boolean | null {
    return this.reach([type, true], (inner) => {
      if (inner.isUnionType() || inner.isIntersectionType()) {
        const parts = this.ask(() => inner.getTypes() ?? []);
        return parts && parts.map((part): [Type, boolean] => [part, true]);
      }
      if (!isTypeReference(inner)) return [];
      const args = this.ask(() => this.checker.getTypeArguments(inner));
      return args && args.map((arg): [Type, boolean] => [arg, true]);
    }, this.values);
  }

  /** Whether a place of type `target` takes a value of type `source` as it
   * would one typed `unknown` at each positive `any` of `source`: `unknown`
   * there or, below the place itself, the same type; through unions,
   * intersections, the arguments of one generic type, properties by name,
   * index signatures by key, and signatures' results. `null` where the
   * inspection cannot finish. A pair met again while it is being compared
   * holds unless another obligation fails. */
  takes(source: Type, target: Type): boolean | null {
    return this.takesAll([[source, target, true]]);
  }

  private takesAll(start: [Type, Type, boolean][]): boolean | null {
    const queue = [...start];
    const seen: string[] = [];
    const visited = new Set<string>();
    let failed = false;
    for (let i = 0; i < queue.length; i++) {
      const pair = queue[i];
      if (!pair) continue;
      const [source, target, place] = pair;
      if (target.flags & TypeFlags.Unknown) continue;
      // A place typed `any` takes a value that is no `any` as it is: what
      // the value holds is `any` there already, and reported where it is read.
      if (target.flags & TypeFlags.Any && !(source.flags & TypeFlags.Any)) continue;
      if (source.flags & TypeFlags.Any) {
        if (!place && source.id === target.id) continue;
        return false;
      }
      if (source.id === target.id || this.canonical(source) === this.canonical(target)) continue;
      const held = this.holds(source);
      if (held === false) continue;
      if (held === null) {
        failed = true;
        continue;
      }
      const key = `${this.canonical(source)}>${this.canonical(target)}`;
      const known = this.taking.get(key);
      if (known === false) return false;
      if (known === true || visited.has(key)) continue;
      visited.add(key);
      seen.push(key);
      const next = this.obligations(source, target);
      if (next === null) {
        failed = true;
        continue;
      }
      if (next === false) {
        this.taking.set(key, false);
        return false;
      }
      for (const [from, to] of next) queue.push([from, to, false]);
    }
    if (failed) return null;
    for (const key of seen) this.taking.set(key, true);
    return true;
  }

  /** What `target` taking `source` requires one step down: pairs that must
   * each hold, `false` where it cannot hold, `null` where the compiler's API
   * fails. A union target is decided here, by its first member that takes
   * the source. */
  private obligations(source: Type, target: Type): [Type, Type][] | false | null {
    const checker = this.checker;
    if (source.isUnionType()) {
      const parts = this.ask(() => source.getTypes() ?? []);
      return parts && parts.map((part): [Type, Type] => [part, target]);
    }
    if (target.isUnionType()) {
      const parts = this.ask(() => target.getTypes() ?? []);
      if (!parts) return null;
      let result: false | null = false;
      for (const part of parts) {
        const taken = this.takesAll([[source, part, false]]);
        if (taken) return [];
        if (taken === null) result = null;
      }
      return result;
    }
    if (target.isIntersectionType()) {
      const parts = this.ask(() => target.getTypes() ?? []);
      return parts && parts.map((part): [Type, Type] => [source, part]);
    }
    // A place with no positions of its own (`object`, a primitive, a type
    // parameter) reads nothing the value holds.
    if (!target.isObjectType()) return [];
    if (isTypeReference(source) && isTypeReference(target)) {
      const from = this.ask(() => source.getTarget());
      const to = this.ask(() => target.getTarget());
      if (!from || !to) return null;
      if (from.id === to.id && from.id !== source.id) {
        const sourceArgs = this.ask(() => checker.getTypeArguments(source));
        const targetArgs = this.ask(() => checker.getTypeArguments(target));
        if (!sourceArgs || !targetArgs) return null;
        if (sourceArgs.length === targetArgs.length)
          return sourceArgs.map((arg, i): [Type, Type] => [arg, targetArgs[i] ?? arg]);
      }
    }
    const pairs: [Type, Type][] = [];
    const properties = this.ask(() => checker.getPropertiesOfType(target));
    if (!properties) return null;
    for (const property of properties) {
      const from = this.ask(() => checker.getPropertyOfType(source, property.name));
      if (from === null) return null;
      if (!from) continue;
      const types = this.ask(() => checker.getTypeOfSymbol([from, property]));
      if (!types) return null;
      const [sourceType, targetType] = types;
      if (sourceType && targetType) pairs.push([sourceType, targetType]);
    }
    const sourceIndexes = this.ask(() => checker.getIndexInfosOfType(source));
    const targetIndexes = this.ask(() => checker.getIndexInfosOfType(target));
    if (!sourceIndexes || !targetIndexes) return null;
    for (const index of targetIndexes) {
      const from = sourceIndexes.find((info) => info.keyType.id === index.keyType.id);
      if (from) pairs.push([from.valueType, index.valueType]);
    }
    for (const kind of [SignatureKind.Call, SignatureKind.Construct]) {
      const sourceSignatures = this.ask(() => checker.getSignaturesOfType(source, kind));
      const targetSignatures = this.ask(() => checker.getSignaturesOfType(target, kind));
      if (!sourceSignatures || !targetSignatures) return null;
      for (const [i, signature] of targetSignatures.entries()) {
        const from = sourceSignatures[i] ?? sourceSignatures[sourceSignatures.length - 1];
        if (!from) continue;
        const fromResult = this.ask(() => checker.getReturnTypeOfSignature(from));
        const toResult = this.ask(() => checker.getReturnTypeOfSignature(signature));
        if (fromResult === null || toResult === null) return null;
        if (fromResult && toResult) pairs.push([fromResult, toResult]);
      }
    }
    return pairs;
  }
}

/** A place that reads a value only as it would read one typed `unknown`:
 * the operand of `typeof`, `!`, `void` and `throw`, of an equality and of a
 * template, a condition, and an expression statement, which discards it. */
function readsAsUnknown(node: Node): boolean {
  const parent = node.parent;
  if (!parent) return false;
  if (ts.isTypeOfExpression(parent) || ts.isVoidExpression(parent) || ts.isThrowStatement(parent) ||
    ts.isTemplateSpan(parent) || ts.isExpressionStatement(parent)) return true;
  if (ts.isPrefixUnaryExpression(parent)) return parent.operator === ts.SyntaxKind.ExclamationToken;
  if (ts.isBinaryExpression(parent)) return EQUALITY.includes(parent.operatorToken.kind);
  if (ts.isIfStatement(parent) || ts.isWhileStatement(parent) || ts.isDoStatement(parent))
    return parent.expression === node;
  if (ts.isConditionalExpression(parent)) return parent.condition === node;
  if (ts.isForStatement(parent)) return parent.condition === node;
  return false;
}

/** Whether `name` at `node` is the standard library's global of that name. */
function libraryGlobal(node: Node, names: readonly string[], checker: Checker, program: Program): boolean {
  if (!ts.isIdentifier(node) || !names.includes(node.text)) return false;
  const declarations = checker.getSymbolAtLocation(node)?.declarations ?? [];
  return declarations.length > 0 && declarations.every((declaration) => {
    const file = declaration.resolve()?.getSourceFile();
    return file !== undefined && program.isSourceFileDefaultLibrary(file);
  });
}

/** The standard library's `JSON.parse` of one text. */
function parseOfText(node: Node, checker: Checker, program: Program): boolean {
  if (!ts.isCallExpression(node) || node.arguments.length !== 1) return false;
  const callee = node.expression;
  return ts.isPropertyAccessExpression(callee) && callee.name.text === "parse" &&
    libraryGlobal(callee.expression, ["JSON"], checker, program);
}

/** `new Map()` or `new Set()` of the standard library, without arguments. */
function emptyCollection(node: Node, checker: Checker, program: Program): boolean {
  return ts.isNewExpression(node) && !node.typeArguments && !node.arguments?.length &&
    libraryGlobal(node.expression, ["Map", "Set"], checker, program);
}

/** Whether `node` initializes a binding pattern, `const [a, b] = node`. */
function patternInitializer(node: Node): boolean {
  const parent = node.parent;
  if (!parent || !(ts.isVariableDeclaration(parent) || ts.isParameterDeclaration(parent) || ts.isBindingElement(parent)) ||
    parent.initializer !== node) return false;
  const name: Node | undefined = parent.name;
  return !!name && (ts.isObjectBindingPattern(name) || ts.isArrayBindingPattern(name));
}

/** Whether argument `node` is bound to a parameter typed by a type parameter
 * of the signature the call resolves to, which the call infers from it. */
function inferredBinding(node: Node, checker: Checker): boolean {
  const call = node.parent;
  if (!call || !(ts.isCallExpression(call) || ts.isNewExpression(call))) return false;
  const index = (call.arguments ?? []).findIndex((argument) => argument === node);
  if (index < 0) return false;
  const resolved = checker.getResolvedSignature(call);
  const generic = resolved?.getTarget() ?? resolved;
  if (!generic) return false;
  const binders = new Set(generic.getTypeParameters().map((binder) => binder.id));
  const declared = checker.getParameterType(generic, index);
  return declared !== undefined && declared.isTypeParameter() && binders.has(declared.id);
}

/* ------------------------------------------------------------ the walk -- */

/** A node whose value type is checked: an expression or a declaration's
 * name, outside types, imports and exports. Left out are the nodes whose
 * value is another's, checked there: the member name of a property access
 * and the name of an object literal's property (the access, the property's
 * value), a parenthesized expression, a conditional and a logical operator
 * (their operands); and an empty array literal, which holds no value. */
function valued(node: Node): boolean {
  const parent = node.parent;
  if (parent && (ts.isPropertyAccessExpression(parent) || ts.isPropertyAssignment(parent)) && parent.name === node)
    return false;
  if (ts.isParenthesizedExpression(node) || ts.isConditionalExpression(node)) return false;
  if (ts.isBinaryExpression(node) && LOGICAL.includes(node.operatorToken.kind)) return false;
  if (ts.isArrayLiteralExpression(node) && node.elements.length === 0) return false;
  return ts.isExpression(node);
}

/** A subtree holding no value: a type, an import or export, a type
 * declaration, a heritage clause. */
function typeOnly(node: Node): boolean {
  return ts.isTypeNode(node) || ts.isImportDeclaration(node) || ts.isExportDeclaration(node) ||
    ts.isInterfaceDeclaration(node) || ts.isTypeAliasDeclaration(node) || ts.isHeritageClause(node);
}

/** The type of each node, `null` where the compiler's API fails to return
 * it. */
function typesOf(checker: Checker, nodes: Node[]): (Type | undefined | null)[] {
  try {
    return checker.getTypeAtLocation(nodes);
  } catch {
    if (nodes.length === 1) return [null];
    const half = Math.ceil(nodes.length / 2);
    return [...typesOf(checker, nodes.slice(0, half)), ...typesOf(checker, nodes.slice(half))];
  }
}

/** The project's checker and what a check reads from it. */
interface Context {
  checker: Checker;
  program: Program;
  inspection: Inspection;
  /** `Json`, the parsed data the decoders read. */
  json: Type;
}

/** Everything found in one file, in source order. */
function findIn(file: string, source: SourceFile, context: Context): Found[] {
  const { checker, program, inspection, json } = context;
  const text = fs.readFileSync(file, "utf8");
  const lines = text.split("\n");
  const found: Found[] = [];
  const at = (node: Node, kind: Kind, note: string = ""): void => {
    const where = source.getLineAndCharacterOfPosition(node.getStart(source));
    found.push({
      file,
      line: where.line + 1,
      column: where.character + 1,
      kind,
      text: `${note}${lines[where.line]?.trim() ?? ""}`,
      reason: REASONED.includes(kind) ? reasonAt(lines, where.line) : null,
    });
  };
  // Nodes in post-order, each with whether it holds a value to type.
  const order: Node[] = [];
  const walk = (node: Node, moduleLevel: boolean): void => {
    const written = WRITTEN.find(([syntax]) => syntax === node.kind)?.[1];
    if (written !== undefined && !assertsNothing(node)) at(node, written);
    for (const [fn, missing] of boundary(checker, node, moduleLevel))
      if (missing.length) at(fn, "unannotated", `${missing.join(", ")}: `);
    if (!typeOnly(node)) {
      const inner = moduleLevel && (ts.isVariableStatement(node) || ts.isVariableDeclarationList(node));
      node.forEachChild((child) => walk(child, inner));
      if (valued(node)) order.push(node);
    } else node.forEachChild((child) => walk(child, false));
  };
  source.forEachChild((child) => walk(child, true));
  const types = typesOf(checker, order);
  // A node whose `any` comes from one reported inside it is not reported again.
  const reported = new Set<Node>();
  const within = (node: Node): boolean => {
    let hit = false;
    const look = (child: Node): void => {
      if (hit) return;
      if (reported.has(child)) hit = true;
      else child.forEachChild(look);
    };
    node.forEachChild(look);
    return hit;
  };
  order.forEach((node, index) => {
    const type = types[index];
    if (type === null) {
      at(node, "uninspected");
      return;
    }
    if (!type) return;
    const value = inspection.isAny(type);
    if (value === null) return at(node, "uninspected");
    const report = (): void => {
      if (within(node)) return;
      reported.add(node);
      at(node, "typed any");
    };
    const declared = ts.isIdentifier(node) && node.parent && "name" in node.parent && node.parent.name === node;
    if (declared) {
      if (value) report();
      return;
    }
    // A member's receiver holding `any` only inside (`xs.map` of an `any[]`):
    // the member's own type is checked, and what it passes on, such as a
    // callback's parameter, is checked where it is declared.
    const parent = node.parent;
    if (parent && (ts.isPropertyAccessExpression(parent) || ts.isElementAccessExpression(parent)) &&
      parent.expression === node && !(type.flags & TypeFlags.Any)) return;
    if (value && readsAsUnknown(node)) return;
    const place = ts.isExpression(node) ? checker.getContextualType(node) : undefined;
    if (!place) {
      if (value) report();
      return;
    }
    // A place at the value's own type adds no assumption, and neither does
    // the initializer of a binding pattern, whose names are checked as
    // declarations.
    if ((place.id === type.id && !value) || patternInitializer(node)) return;
    if (value && inferredBinding(node, checker)) return report();
    if (value && emptyCollection(node, checker, program) && inspection.isAny(place) === false) return;
    if (value && !(place.flags & TypeFlags.Any) && parseOfText(node, checker, program) && checker.isTypeAssignableTo(json, place)) return;
    const taken = inspection.takes(type, place);
    if (taken === null) at(node, "uninspected");
    else if (!taken) report();
  });
  return found.sort((a, b) => a.line - b.line || a.column - b.column);
}

/** The comment marking a line a fixture expects reported, and its kind. */
const EXPECTED = /\/\/ expected: ([\w !,]+)$/;

/** The files of the project of `config`, and what is found in those of
 * them whose position in the sorted list is `part` modulo `parts`. */
function check(config: string, part: number, parts: number): { files: string[]; found: Found[] } {
  const api = new API({ cwd: path.dirname(config) });
  const project = api.updateSnapshot({ openProjects: [config] }).getProject(config);
  if (!project) throw new Error(`the compiler did not open ${config}`);
  const calculus = project.program.getSourceFile(path.resolve(import.meta.dirname, "calculus.mts"));
  const alias = calculus?.statements.find((s) => ts.isTypeAliasDeclaration(s) && s.name.text === "Json");
  const json = alias && ts.isTypeAliasDeclaration(alias) ? project.checker.getTypeAtLocation(alias.name) : undefined;
  if (!json) throw new Error(`the project of ${config} reads no type Json from tools/calculus.mts`);
  const context: Context = { checker: project.checker, program: project.program, inspection: new Inspection(project.checker), json };
  const files = project.rootFiles.map((file) => path.relative(".", file)).sort();
  const found = files.filter((_, i) => i % parts === part).flatMap((file) => {
    const source = project.program.getSourceFile(path.resolve(file));
    if (!source) throw new Error(`the compiler produced no tree for ${file}`);
    return findIn(file, source, context);
  });
  api.close();
  return { files, found };
}

/** Whether a worker's output is its result, field by field. */
function isResult(value: unknown): value is { files: string[]; found: Found[] } {
  if (!value || typeof value !== "object" || !("files" in value) || !("found" in value)) return false;
  const { files, found } = value;
  return Array.isArray(files) && files.every((f: unknown) => typeof f === "string") && Array.isArray(found) &&
    found.every((f: unknown) => !!f && typeof f === "object" && "file" in f && typeof f.file === "string" &&
      "line" in f && typeof f.line === "number" && "column" in f && typeof f.column === "number" &&
      "kind" in f && KINDS.some((k) => k === f.kind) && "text" in f && typeof f.text === "string" &&
      "reason" in f && (f.reason === null || typeof f.reason === "string"));
}

const args = process.argv.slice(2);
const projectAt = args.indexOf("--project");
const projectDir = projectAt < 0 ? "tools" : args[projectAt + 1];
if (projectDir === undefined) throw new Error("usage: unchecked.mts [--list] [--project DIR --expect]");
const config = path.resolve(projectDir, "tsconfig.json");
const workerAt = args.indexOf("--worker");
if (workerAt >= 0) {
  // One part of the files, in a process and a compiler of its own.
  const [part, parts] = (args[workerAt + 1] ?? "").split("/").map(Number);
  if (part === undefined || parts === undefined) throw new Error("--worker PART/PARTS");
  process.stdout.write(JSON.stringify(check(config, part, parts)));
  process.exit(0);
}
// The files are checked in parallel, each part by a compiler of its own.
const parts = Math.max(1, Math.min(8, availableParallelism() - 1));
const results = await Promise.all(Array.from({ length: parts }, (_, part) => new Promise<{ files: string[]; found: Found[] }>((done, fail) => {
  const child = spawn(process.execPath, [fileURLToPath(import.meta.url), "--project", projectDir, "--worker", `${part}/${parts}`],
    { stdio: ["ignore", "pipe", "inherit"] });
  let out = "";
  child.stdout.on("data", (chunk: Buffer) => (out += chunk.toString()));
  child.on("close", (code) => {
    const parsed: unknown = code === 0 ? JSON.parse(out) : undefined;
    if (isResult(parsed)) done(parsed);
    else fail(new Error(`part ${part} of ${parts} of unchecked.mts failed (${code})`));
  });
})));
const files = results[0]?.files ?? [];
const found = results.flatMap((result) => result.found)
  .sort((a, b) => a.file.localeCompare(b.file) || a.line - b.line || a.column - b.column);
// One line per site and report: a declaration and its initializer typed `any`
// on one line are one site.
const sites = found.filter((w, i) =>
  !found.slice(0, i).some((v) => v.file === w.file && v.line === w.line && v.kind === w.kind));
const show = (w: Found): string => `${w.file}:${w.line}:${w.column}  [${w.kind}]  ${w.text}`;
if (args.includes("--expect")) {
  // Every report on a line expecting its kind, and every expectation met.
  const expected = files.flatMap((file) =>
    fs.readFileSync(file, "utf8").split("\n").flatMap((line, i) => {
      const kinds = EXPECTED.exec(line)?.[1];
      return kinds === undefined ? [] : kinds.split(/, */).map((kind) => ({ file, line: i + 1, kind }));
    }));
  const unexpected = sites.filter((w) => !expected.some((e) => e.file === w.file && e.line === w.line && e.kind === w.kind));
  const missed = expected.filter((e) => !sites.some((w) => w.file === e.file && w.line === e.line && w.kind === e.kind));
  for (const w of unexpected) console.log(`unexpected: ${show(w)}`);
  for (const e of missed) console.log(`missed: ${e.file}:${e.line}  [${e.kind}]`);
  console.log(`${expected.length} expected reports, ${expected.length - missed.length} made, ${unexpected.length} unexpected`);
  process.exitCode = unexpected.length || missed.length ? 1 : 0;
} else {
  const failing = sites.filter((w) => w.reason === null);
  if (args.includes("--list"))
    for (const w of sites) console.log(`${show(w)}${w.reason === null ? "" : `\n    asserted: ${w.reason}`}`);
  else for (const w of failing) console.log(`${REASONED.includes(w.kind) ? "no reason" : "error"}: ${show(w)}`);
  const counts = KINDS.map((kind) => `${sites.filter((w) => w.kind === kind).length} \`${kind}\``);
  console.log(`\n${counts.join(", ")} in ${new Set(sites.map((w) => w.file)).size} of ${files.length} files;` +
    ` ${sites.length - failing.length} assertions with a reason, ${failing.length} errors`);
  process.exitCode = failing.length ? 1 : 0;
}
