#!/usr/bin/env node
/**
 * Everywhere the node side tells the compiler not to check something, or
 * leaves a unit's boundary unstated, found with the compiler the project
 * builds with. `tsc` has no option for these, and `typescript-eslint` cannot
 * check them here because it does not support TypeScript 7.
 *
 * The node side is every file `tools/tsconfig.json` includes. Five reports:
 *
 * A written `any` is not a weaker type, it is the absence of one: the compiler
 * stops reading the expression, so a field that does not exist reads as
 * `undefined` rather than failing. That is not hypothetical here — two checks
 * on type-parameter defaults read `tp.default` through an `any` for as long as
 * they existed, and never once fired.
 *
 * A value the checker types `any` is the same absence, arriving from a
 * library (`JSON.parse`, a member a declaration file leaves untyped) or from
 * an array literal no annotation types (`let xs = []`). Such a value may flow
 * only into a place typed `unknown`, where the code then narrows it: an
 * expression whose type contains `any` (itself, a union member or a type
 * argument) is reported unless its contextual type is `unknown`, and so is a
 * declaration whose type contains `any`. Each report names where the `any`
 * arises; what it then flows into is not reported again.
 *
 * A function without annotations leaves its boundary to inference. Every
 * function declaration, method, accessor and constructor, and every arrow or
 * function expression bound to a module-level name or a class field, states
 * the type of each parameter and, but for a constructor or a setter, its
 * result (a module binding may instead state the function's type on the
 * binding). What lies inside a unit is inferred and checked there: a local
 * `const` or `let`, and an arrow or function expression written as an
 * argument or anywhere else inside a function, which its context types.
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
import fs from "node:fs";
import path from "node:path";
import { API, TypeFlags, isTypeReference, type Checker, type Program, type Type } from "typescript/unstable/sync";
import * as ts from "typescript/unstable/ast";
import type { Node, SourceFile } from "typescript/unstable/ast";

/** What was found, which report it is, and the reason written with it. */
type Kind = "any" | "as" | "!" | "typed any" | "unannotated" | "untyped";
interface Found {
  file: string;
  line: number;
  column: number;
  kind: Kind;
  text: string;
  reason: string | null;
}

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

/** What a function-like declaration leaves unstated: each parameter without
 * a type, and its result where it has one to state. */
function unstated(node: ts.SignatureDeclaration, result: boolean): string[] {
  const missing = node.parameters
    .filter((parameter) => parameter.type === undefined)
    .map((parameter) => `parameter ${parameter.name.getText()}`);
  return result && node.type === undefined ? [...missing, "result"] : missing;
}

/** The function an initializer holds, through parentheses. */
function functionValue(node: Node | undefined): ts.ArrowFunction | ts.FunctionExpression | null {
  if (node === undefined) return null;
  if (ts.isParenthesizedExpression(node)) return functionValue(node.expression);
  return ts.isArrowFunction(node) || ts.isFunctionExpression(node) ? node : null;
}

/** What a declaration at a unit's boundary leaves unstated, or `[]`. */
function boundary(node: Node, moduleLevel: boolean): string[] {
  if (ts.isFunctionDeclaration(node)) return unstated(node, true);
  // An object literal's method is typed by its context, as an argument is.
  const member = node.parent !== undefined && ts.isClassLikeDeclaration(node.parent);
  if (member && (ts.isMethodDeclaration(node) || ts.isGetAccessorDeclaration(node))) return unstated(node, true);
  if (ts.isConstructorDeclaration(node) || (member && ts.isSetAccessorDeclaration(node))) return unstated(node, false);
  if ((moduleLevel && ts.isVariableDeclaration(node)) || ts.isPropertyDeclaration(node)) {
    const value = functionValue(node.initializer);
    return value && node.type === undefined ? unstated(value, true) : [];
  }
  return [];
}

/** Whether `type` contains `any`: itself, a member of a union or an
 * intersection, or an argument of a type reference, to a bounded depth. */
function containsAny(checker: Checker, type: Type, depth: number = 0): boolean | null {
  if (type.isErrorType() || depth > 4) return false;
  if (type.flags & TypeFlags.Any) return true;
  let parts: readonly Type[] = [];
  try {
    if (type.isUnionType() || type.isIntersectionType()) parts = type.getTypes() ?? [];
    else if (isTypeReference(type)) parts = checker.getTypeArguments(type);
  } catch {
    return null;
  }
  let unknown = false;
  for (const part of parts) {
    const inner = containsAny(checker, part, depth + 1);
    if (inner) return true;
    if (inner === null) unknown = true;
  }
  return unknown ? null : false;
}

/** The parts of a union or intersection, the arguments of a type reference;
 * `null` where the compiler's API fails to return them. */
function partsOf(checker: Checker, type: Type): { parts: readonly Type[]; target: number | null } | null {
  try {
    if (type.isUnionType() || type.isIntersectionType()) return { parts: type.getTypes() ?? [], target: null };
    if (isTypeReference(type)) return { parts: checker.getTypeArguments(type), target: type.getTarget().id };
    return { parts: [], target: null };
  } catch {
    return null;
  }
}

/** Whether a place of type `target` takes a value of type `source` as it
 * would one typed `unknown` at each `any` of `source`: `unknown` or `any`
 * there, through unions and the arguments of one generic type. */
function takes(checker: Checker, source: Type, target: Type, depth: number = 0): boolean {
  if (target.flags & (TypeFlags.Unknown | TypeFlags.Any)) return true;
  if (containsAny(checker, source) === false) return true;
  if (depth > 4 || source.flags & TypeFlags.Any) return false;
  const from = partsOf(checker, source);
  const to = partsOf(checker, target);
  if (!from || !to) return false;
  if (source.isUnionType()) return from.parts.every((part) => takes(checker, part, target, depth + 1));
  if (target.isUnionType()) return to.parts.some((part) => takes(checker, source, part, depth + 1));
  return from.target !== null && from.target === to.target && from.parts.length === to.parts.length &&
    from.parts.every((part, i) => {
      const into = to.parts[i];
      return into !== undefined && takes(checker, part, into, depth + 1);
    });
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

const EQUALITY: number[] = [
  ts.SyntaxKind.EqualsEqualsEqualsToken,
  ts.SyntaxKind.ExclamationEqualsEqualsToken,
  ts.SyntaxKind.EqualsEqualsToken,
  ts.SyntaxKind.ExclamationEqualsToken,
];

/** The library's `JSON.parse` of one text, typed `any` by its declaration:
 * the reviewed overlay of library globals states its result as parsed data
 * (`ParsedJson` in library-globals.mts), which `Json` in calculus.mts is. */
function parseOfText(node: Node, checker: Checker, program: Program): boolean {
  if (!ts.isCallExpression(node) || node.arguments.length !== 1) return false;
  const callee = node.expression;
  if (!ts.isPropertyAccessExpression(callee) || callee.name.text !== "parse" || !ts.isIdentifier(callee.expression) ||
    callee.expression.text !== "JSON") return false;
  const declarations = checker.getSymbolAtLocation(callee.expression)?.declarations ?? [];
  return declarations.length > 0 && declarations.every((declaration) => {
    const file = declaration.resolve()?.getSourceFile();
    return file !== undefined && program.isSourceFileDefaultLibrary(file);
  });
}

/** A construction without arguments, `new Map()`: it holds no value, and
 * the type arguments TypeScript gives it from none are those of the place it
 * flows to. */
function emptyConstruction(node: Node): boolean {
  return ts.isNewExpression(node) && !node.typeArguments && !node.arguments?.length;
}

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

const LOGICAL: number[] = [
  ts.SyntaxKind.AmpersandAmpersandToken,
  ts.SyntaxKind.BarBarToken,
  ts.SyntaxKind.QuestionQuestionToken,
];

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
  } catch (error) {
    if (nodes.length === 1) return [null];
    const half = Math.ceil(nodes.length / 2);
    return [...typesOf(checker, nodes.slice(0, half)), ...typesOf(checker, nodes.slice(half))];
  }
}

/** Everything found in one file, in source order. */
function findIn(file: string, source: SourceFile, checker: Checker, program: Program, json: Type): Found[] {
  const text = fs.readFileSync(file, "utf8");
  const lines = text.split("\n");
  const found: Found[] = [];
  const at = (node: Node, kind: Kind): void => {
    const where = source.getLineAndCharacterOfPosition(node.getStart(source));
    found.push({
      file,
      line: where.line + 1,
      column: where.character + 1,
      kind,
      text: lines[where.line]?.trim() ?? "",
      reason: REASONED.includes(kind) ? reasonAt(lines, where.line) : null,
    });
  };
  // Nodes in post-order, each with whether it holds a value to type.
  const order: Node[] = [];
  const walk = (node: Node, moduleLevel: boolean): void => {
    const written = WRITTEN.find(([syntax]) => syntax === node.kind)?.[1];
    if (written !== undefined && !assertsNothing(node)) at(node, written);
    const missing = boundary(node, moduleLevel);
    if (missing.length) {
      at(node, "unannotated");
      const last = found[found.length - 1];
      if (last) last.text = `${missing.join(", ")}: ${last.text}`;
    }
    if (!typeOnly(node)) {
      const inner = moduleLevel && (ts.isVariableStatement(node) || ts.isVariableDeclarationList(node));
      node.forEachChild((child) => walk(child, inner));
      if (valued(node)) order.push(node);
    } else node.forEachChild((child) => walk(child, false));
  };
  source.forEachChild((child) => walk(child, true));
  const types = typesOf(checker, order);
  for (const [index, type] of types.entries()) if (type === null) at(order[index] ?? source, "untyped");
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
    if (!type) return;
    const any = containsAny(checker, type);
    if (any === null) at(node, "untyped");
    if (!any || within(node)) return;
    const declared = ts.isIdentifier(node) && node.parent && "name" in node.parent && node.parent.name === node;
    if (!declared && readsAsUnknown(node)) return;
    // A member's receiver holding `any` only inside (`xs.map` of an `any[]`):
    // the member's own type is checked, and what it passes on, such as a
    // callback's parameter, is checked where it is declared.
    const parent = node.parent;
    if (parent && (ts.isPropertyAccessExpression(parent) || ts.isElementAccessExpression(parent)) &&
      parent.expression === node && !(type.flags & TypeFlags.Any)) return;
    const context = declared || !ts.isExpression(node) ? undefined : checker.getContextualType(node);
    if (context && (emptyConstruction(node) ? containsAny(checker, context) === false : takes(checker, type, context)))
      return;
    if (context && parseOfText(node, checker, program) && checker.isTypeAssignableTo(json, context)) return;
    reported.add(node);
    at(node, "typed any");
  });
  return found.sort((a, b) => a.line - b.line || a.column - b.column);
}

const config = path.resolve("tools/tsconfig.json");
const api = new API({ cwd: path.dirname(config) });
const project = api.updateSnapshot({ openProjects: [config] }).getProject(config);
if (!project) throw new Error(`the compiler did not open ${config}`);
// `Json`, the type of parsed data the decoders read.
const calculus = project.program.getSourceFile(path.resolve("tools/calculus.mts"));
const alias = calculus?.statements.find((s) => ts.isTypeAliasDeclaration(s) && s.name.text === "Json");
const json = alias && ts.isTypeAliasDeclaration(alias) ? project.checker.getTypeAtLocation(alias.name) : undefined;
if (!json) throw new Error("tools/calculus.mts declares no type Json");
const files = project.rootFiles.map((file) => path.relative(".", file)).sort();
const found = files.flatMap((file) => {
  const source = project.program.getSourceFile(path.resolve(file));
  if (!source) throw new Error(`the compiler produced no tree for ${file}`);
  return findIn(file, source, project.checker, project.program, json);
});
api.close();
// One line per site and report: a declaration and its initializer typed `any`
// on one line are one site.
const sites = found.filter((w, i) =>
  !found.slice(0, i).some((v) => v.file === w.file && v.line === w.line && v.kind === w.kind));
const failing = sites.filter((w) => w.reason === null);
const show = (w: Found): string => `${w.file}:${w.line}:${w.column}  [${w.kind}]  ${w.text}`;
if (process.argv.includes("--list"))
  for (const w of sites) console.log(`${show(w)}${w.reason === null ? "" : `\n    asserted: ${w.reason}`}`);
else for (const w of failing) console.log(`${REASONED.includes(w.kind) ? "no reason" : "error"}: ${show(w)}`);
const KINDS: Kind[] = ["any", "typed any", "unannotated", "untyped", "as", "!"];
const counts = KINDS.map((kind) => `${sites.filter((w) => w.kind === kind).length} \`${kind}\``);
console.log(`\n${counts.join(", ")} in ${new Set(sites.map((w) => w.file)).size} of ${files.length} files;` +
  ` ${sites.length - failing.length} assertions with a reason, ${failing.length} errors`);
process.exitCode = failing.length ? 1 : 0;
