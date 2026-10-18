#!/usr/bin/env node
/**
 * Everywhere the node side tells the compiler not to check something, or
 * leaves a unit's boundary unstated, found with the compiler the project
 * builds with. `tsc` has no option for these, and `typescript-eslint` cannot
 * check them here because it does not support TypeScript 7.
 *
 *   node tools/unchecked.mts [--list] [--project DIR --expect] [--contracts]
 *
 * The node side is every file `tools/tsconfig.json` includes. With
 * `--project`, the files another project's `tsconfig.json` includes; with
 * `--expect`, every report must fall on a line ending in the comment
 * `// expected: KIND` and every such line must be reported, which is how
 * `tests/unchecked-project/` holds the counterexamples each report exists
 * for; with `--contracts`, the external inputs typed `any` the shadow program
 * reads at a reviewed contract.
 *
 * A written `any` is not a weaker type, it is the absence of one: the compiler
 * stops reading the expression, so a field that does not exist reads as
 * `undefined` rather than failing. That is not hypothetical here — two checks
 * on type-parameter defaults read `tp.default` through an `any` for as long as
 * they existed, and never once fired.
 *
 * A value the checker types `any` is the same absence, arriving from a
 * library (`JSON.parse`, a member a declaration file leaves untyped) or from
 * an array literal no annotation types (`let xs = []`). The program is
 * checked a second time, as the shadow program: TypeScript reads each
 * external declaration file (the standard library, Node's types, the
 * compiler API's) at the contracts `shadow-contracts.mts` states, in which
 * no `any` is left, and checks the program's own sources over them. Each
 * error it reports there is an `[any flow]`: a place the program relies on
 * an external `any`. TypeScript's assignability, inference and overload
 * resolution decide every flow (calls, rest and spread arguments, written,
 * inferred and defaulted type arguments, returns, destructuring, member
 * reads, operators). A value of the program the shadow program still types
 * `any` (itself, a member of a union or an intersection, or a type argument,
 * at any depth) is a `[typed any]`: a written `any`, an array literal no
 * annotation types, or one the checker gives without a declaration (a
 * dynamic `import()`, a call of `Function`) unless it is bound straight to a
 * place typed `unknown`. A report is made where the `any` arises; what it
 * then flows into is not reported again. A node whose type the compiler's
 * API does not return is `[uninspected]`.
 *
 * What lies outside: a program free of `any` may still break a type by
 * mutation (`Object.assign(target, r)` overwrites `target`'s fields), by a
 * callback's effects, by a guard or an assertion that does not hold, or
 * through a native contract its declaration misstates. TypeScript's own
 * unsound rules (method parameter bivariance among them) stay as they are.
 * Those are what TScert verifies, not this check.
 *
 * A function without annotations leaves its boundary to inference.
 * `[unannotated]`: every function declaration; a class's methods, accessors
 * and constructor and every function its fields hold; an object literal's
 * methods, accessors and function-valued properties, unless a written type
 * gives the literal its contextual type; and every function a module binding
 * or `export default` holds as its value or an element of it (through
 * parentheses, assertions, `await`, a comma's last operand, an assignment's
 * right side, conditionals, logical operators, array literals and their
 * spreads), unless a type gives it its contextual type. Each states the type of every parameter and, but for a
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
import { API, TypeFlags, isTypeReference, type Checker, type Program, type Type } from "typescript/unstable/sync";
import * as ts from "typescript/unstable/ast";
import type { Node, SourceFile } from "typescript/unstable/ast";
import { isHostFile } from "./compiler-api.mts";
import { PRELUDE, shadowText, type ReplacedInput } from "./shadow-contracts.mts";

/** What was found, which report it is, and the reason written with it. */
type Kind = "any" | "as" | "!" | "any flow" | "typed any" | "unannotated" | "uninspected";
interface Found {
  file: string;
  line: number;
  column: number;
  kind: Kind;
  text: string;
  reason: string | null;
}

const KINDS: Kind[] = ["any", "any flow", "typed any", "unannotated", "uninspected", "as", "!"];

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

/* ------------------------------------------------------ the boundaries -- */

/** What a function-like declaration leaves unstated: each parameter without
 * a type, and its result where it has one to state. */
function unstated(node: ts.SignatureDeclaration, result: boolean): string[] {
  const missing = node.parameters
    .filter((parameter) => parameter.type === undefined)
    .map((parameter) => `parameter ${parameter.name.getText()}`);
  return result && node.type === undefined ? [...missing, "result"] : missing;
}

/** The function expressions written in `node` that may be its value or an
 * element of it: every subexpression whose value may become the whole's
 * (an operand of parentheses, an assertion, `await`, a comma's last, an
 * assignment's right side, a conditional's branches, a logical operator's
 * operands) and an array literal's elements and spreads. A function
 * written as an argument, a property or a body is the call's, the object
 * literal's or the function's, not the value's. */
function heldFunctions(node: Node | undefined): (ts.ArrowFunction | ts.FunctionExpression)[] {
  if (node === undefined) return [];
  if (ts.isArrowFunction(node) || ts.isFunctionExpression(node)) return [node];
  if (ts.isParenthesizedExpression(node) || ts.isAsExpression(node) || ts.isSatisfiesExpression(node) ||
    ts.isNonNullExpression(node) || ts.isAssertionExpression(node) || ts.isAwaitExpression(node) ||
    ts.isSpreadElement(node)) return heldFunctions(node.expression);
  if (ts.isConditionalExpression(node)) return [...heldFunctions(node.whenTrue), ...heldFunctions(node.whenFalse)];
  if (ts.isBinaryExpression(node)) {
    const operator = node.operatorToken.kind;
    if (LOGICAL.includes(operator) || LOGICAL_ASSIGNMENT.includes(operator))
      return [...heldFunctions(node.left), ...heldFunctions(node.right)];
    if (operator === ts.SyntaxKind.CommaToken || operator === ts.SyntaxKind.EqualsToken) return heldFunctions(node.right);
    return [];
  }
  if (ts.isArrayLiteralExpression(node)) return node.elements.flatMap((element) => heldFunctions(element));
  return [];
}

const LOGICAL_ASSIGNMENT: number[] = [
  ts.SyntaxKind.AmpersandAmpersandEqualsToken,
  ts.SyntaxKind.BarBarEqualsToken,
  ts.SyntaxKind.QuestionQuestionEqualsToken,
];

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

/** Whether a value of `type` is `any`: the type itself, a member of a union
 * or an intersection, or a type argument, at any depth; `null` where the
 * compiler's API does not give a part of it. */
function isAny(checker: Checker, type: Type, seen: Set<number> = new Set<number>()): boolean | null {
  if (type.isErrorType()) return false;
  if (type.flags & TypeFlags.Any) return true;
  if (seen.has(type.id)) return false;
  seen.add(type.id);
  let parts: readonly Type[];
  try {
    parts = type.isUnionType() || type.isIntersectionType() ? type.getTypes() ?? []
      : isTypeReference(type) ? checker.getTypeArguments(type) : [];
  } catch {
    return null;
  }
  let result: boolean | null = false;
  for (const part of parts) {
    const held = isAny(checker, part, seen);
    if (held) return true;
    if (held === null) result = null;
  }
  return result;
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

/** Everything found in one file, in source order: what is written, the
 * boundaries, each error of the shadow program in the file (`any flow`), and
 * each value still typed `any` there (`typed any`). */
function findIn(file: string, source: SourceFile, program: Program, checker: Checker): Found[] {
  const text = fs.readFileSync(file, "utf8");
  const lines = text.split("\n");
  const found: Found[] = [];
  const atLine = (position: number, kind: Kind, note: string = ""): void => {
    const where = source.getLineAndCharacterOfPosition(position);
    found.push({
      file,
      line: where.line + 1,
      column: where.character + 1,
      kind,
      text: `${note}${lines[where.line]?.trim() ?? ""}`,
      reason: REASONED.includes(kind) ? reasonAt(lines, where.line) : null,
    });
  };
  const at = (node: Node, kind: Kind, note: string = ""): void => atLine(node.getStart(source), kind, note);
  for (const diagnostic of program.getSemanticDiagnostics(path.resolve(file)))
    atLine(diagnostic.pos, "any flow", `${diagnostic.text.split("\n")[0] ?? ""}: `);
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
    if (type === null) return at(node, "uninspected");
    if (!type) return;
    const value = isAny(checker, type);
    if (value === null) return at(node, "uninspected");
    if (!value || within(node)) return;
    // A residual `any` the checker gives without a declaration (a dynamic
    // `import()`, a call of `Function`) bound straight to `unknown`.
    const place = ts.isExpression(node) ? checker.getContextualType(node) : undefined;
    if (place && place.flags & TypeFlags.Unknown) return;
    reported.add(node);
    at(node, "typed any");
  });
  return found.sort((a, b) => a.line - b.line || a.column - b.column);
}

/** The comment marking a line a fixture expects reported, and its kind. */
const EXPECTED = /\/\/ expected: ([\w !,]+)$/;

/** The files of the project of `config`, and what is found in those of
 * them whose position in the sorted list is `part` modulo `parts`. The
 * project is checked twice over: as written, to read the external
 * declarations, and as the shadow program, which reads each external
 * declaration file at its contracts (shadow-contracts.mts). */
function check(config: string, part: number, parts: number, inputs: ReplacedInput[] = []): { files: string[]; found: Found[] } {
  const written = new API({ cwd: path.dirname(config) });
  const base = written.updateSnapshot({ openProjects: [config] }).getProject(config);
  if (!base) throw new Error(`the compiler did not open ${config}`);
  const roots = new Set(base.rootFiles);
  const shadow = new API({ cwd: path.dirname(config), fs: {
    readFile: (name) => {
      if (roots.has(name) || !/\.d\.[cm]?ts$/.test(name)) return undefined;
      const declared = base.program.getSourceFile(name);
      if (!declared) throw new Error(`the shadow program reads ${name}, which the written one does not`);
      const { text: shadowed, inputs: replaced } = shadowText(declared, fs.readFileSync(name, "utf8"), isHostFile(name));
      inputs.push(...replaced);
      return name.endsWith(`${path.sep}lib.es5.d.ts`) ? shadowed + PRELUDE : shadowed;
    },
    fileExists: () => undefined,
  } });
  const project = shadow.updateSnapshot({ openProjects: [config] }).getProject(config);
  if (!project) throw new Error(`the compiler did not open the shadow program of ${config}`);
  const broken = [...project.program.getGlobalDiagnostics(), ...project.program.getProgramDiagnostics()];
  if (broken.length) throw new Error(`the shadow program of ${config} does not load: ${broken[0]?.text ?? ""}`);
  const files = [...roots].map((file) => path.relative(".", file)).sort();
  const found = files.filter((_, i) => i % parts === part).flatMap((file) => {
    const source = project.program.getSourceFile(path.resolve(file));
    if (!source) throw new Error(`the compiler produced no tree for ${file}`);
    return findIn(file, source, project.program, project.checker);
  });
  shadow.close();
  written.close();
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
if (args.includes("--contracts")) {
  // The external `any` inputs the shadow program reads at a reviewed
  // contract, once each, for the review.
  const inputs: ReplacedInput[] = [];
  check(config, 0, 1, inputs);
  for (const line of new Set(inputs.map((input) => `${input.contract}: ${input.member}  (${path.basename(input.file)})`)))
    console.log(line);
  process.exit(0);
}
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
const results = await Promise.all<Promise<{ files: string[]; found: Found[] }>[]>(Array.from({ length: parts }, (_, part) => new Promise<{ files: string[]; found: Found[] }>((done, fail) => {
  const child = spawn(process.execPath, [fileURLToPath(import.meta.url), "--project", projectDir, "--worker", `${part}/${parts}`],
    { stdio: ["ignore", "pipe", "inherit"] });
  let out = "";
  child.stdout.on("data", (chunk: unknown) => (out += String(chunk)));
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
