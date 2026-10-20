// The compiler API's guard table generator (HOST-FAMILIES.md, "The guard
// table"): a review aid, outside the front end. It reads every export of
// `typescript/unstable/ast` that the package declares with a type predicate,
// resolved by Node's own resolver through the manifest and the
// re-export chain from the entry point, and accepts its function only under
// the recognition contract; for each accepted guard it computes the exact tag
// set by evaluating the body over every tag value. It prints the table module
// `tools/compiler-api-guards.mts`; `--check` compares it with the reviewed one.
//   node dev/guard-table.mts [--check]
import { readFileSync, realpathSync } from "node:fs";
import { createRequire } from "node:module";
import { dirname, join, relative, resolve } from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";
import { guardClosure } from "../tools/guard-closure.mts";
import { hostPackage, nodeResolve, runtimeConditions } from "../tools/compiler-api.mts";
import { close as closeParser, openText } from "../tools/fragment-parse.mts";
import { syntax as ts } from "../tools/syntax.mts";
import { runDirectory } from "../pipeline/run-directory.mts";

const repository = resolve(import.meta.dirname, "..");
const root = dirname(createRequire(resolve(repository, "tools/package.json")).resolve(`${hostPackage.name}/package.json`));
const entryPoint = "./unstable/ast";
// The conditions Node enables in this process, which activation compares
// with the running Node's.
const conditions: readonly string[] = runtimeConditions();
const isRecord = (v: unknown): v is Record<string, unknown> => typeof v === "object" && v !== null && !Array.isArray(v);
const manifestValue: unknown = JSON.parse(readFileSync(join(root, "package.json"), "utf8"));
if (!isRecord(manifestValue) || typeof manifestValue.name !== "string") throw Error("the package's manifest states no name");
const realRoot = realpathSync(root);
// A specifier as Node's own resolver resolves it from the module that
// contains it (`nodeResolve`), its path in the package.
const resolveSpecifier = (from: string, specifier: string): { module: string } | null => {
  const resolved = nodeResolve(specifier, join(root, from));
  if (resolved === null) return null;
  const module = relative(realRoot, fileURLToPath(resolved));
  return module.startsWith("..") ? null : { module };
};
const entryResolved = resolveSpecifier("package.json", `${manifestValue.name}${entryPoint.slice(1)}`);
if (!entryResolved) throw Error(`Node resolves no ${entryPoint}`);
const entryFile = entryResolved.module;

// The package's modules, parsed once each.
const scratch = runDirectory("tscert-guard-table-");
const parsed = new Map<string, ts.SourceFile>();
const moduleOf = (path: string): ts.SourceFile => {
  const known = parsed.get(path);
  if (known) return known;
  const copy = join(scratch, path.replaceAll("/", "_"));
  const text = readFileSync(join(root, path), "utf8");
  const tree = openText(copy, text);
  parsed.set(path, tree);
  return tree;
};
const specifierText = (node: ts.Expression): string => ts.isStringLiteral(node) ? node.text : "";

// The re-export chain from the entry point to each exported function.
const chains = new Map<string, { module: string; chain: string[] }>();
const walk = (path: string, chain: string[]): void => {
  if (chain.includes(path)) return;
  const tree = moduleOf(path);
  const here = [...chain, path];
  for (const s of tree.statements) {
    if (ts.isFunctionDeclaration(s) && s.name && s.modifiers?.some((m) => m.kind === ts.SyntaxKind.ExportKeyword) &&
        !chains.has(s.name.text))
      chains.set(s.name.text, { module: path, chain: here });
    if (ts.isExportDeclaration(s) && !s.exportClause && s.moduleSpecifier) {
      const next = resolveSpecifier(path, specifierText(s.moduleSpecifier));
      if (next) walk(next.module, here);
    }
  }
};
walk(relative(root, join(root, entryFile)), []);

// The enum the tag constants come from, as Node loads it.
const enumModule = resolveSpecifier("dist/ast/is.generated.js", "#enums/syntaxKind");
if (!enumModule) throw Error("#enums/syntaxKind resolves to no module");
const loaded: unknown = await import(pathToFileURL(join(root, enumModule.module)).href);
const syntaxKind: unknown = isRecord(loaded) ? loaded.SyntaxKind : undefined;
if (!isRecord(syntaxKind)) throw Error("the enum module exports no SyntaxKind");
const constants = new Map<string, number>(Object.entries(syntaxKind).flatMap(([k, v]): [string, number][] =>
  typeof v === "number" ? [[k, v]] : []));
const values = [...new Set(constants.values())].sort((a, b) => a - b);
const nameOf = (value: number): string => [...constants].find(([, v]) => v === value)?.[0] ?? String(value);

// The declared predicates: which exports are guards, and of what.
const declarationFile = (module: string): string => module.replace(/\.js$/, ".d.ts");
const declared = new Map<string, { domain: string; tagged: boolean }>();
for (const { module } of new Set(chains.values())) {
  let tree: ts.SourceFile;
  try { tree = moduleOf(declarationFile(module)); } catch { continue; }
  for (const s of tree.statements)
    if (ts.isFunctionDeclaration(s) && s.name && s.type && ts.isTypePredicateNode(s.type) && s.parameters.length >= 1) {
      const [p] = s.parameters;
      const domain = p?.type ? p.type.getText(tree).trim() : "";
      declared.set(s.name.text, { domain, tagged: domain === "SyntaxKind" });
    }
}

// The recognition contract. A value is a function of the tag value `t`.
type Fail = { reason: string };
type Value = (t: number) => boolean | number;
type Helper = { key: string; text: string };
class Refused extends Error {}
const refuse = (reason: string): never => { throw new Refused(reason); };
type Edge = [string, string, string, string];
const constant = (tree: ts.SourceFile, e: ts.Expression, edges: Map<string, Edge>): number | null => {
  if (ts.isNumericLiteral(e)) return Number(e.text);
  if (ts.isPropertyAccessExpression(e) && ts.isIdentifier(e.expression) && e.expression.text === "SyntaxKind" &&
      [...edges.values()].some(([, local]) => local === "SyntaxKind")) {
    const v = constants.get(e.name.text);
    return v === undefined ? refuse(`SyntaxKind has no member ${e.name.text}`) : v;
  }
  return null;
};
// The module's bindings: its function declarations, never assigned, and its
// named imports from modules of the package, each the module it resolves to
// and the name that module exports; an import with attributes binds nothing.
const bindings = (path: string): { functions: Map<string, ts.FunctionDeclaration>; imports: Map<string, { module: string; name: string }> } => {
  const tree = moduleOf(path);
  const functions = new Map<string, ts.FunctionDeclaration>();
  const imports = new Map<string, { module: string; name: string }>();
  const assigned = new Set<string>();
  const visit = (n: ts.Node): undefined => {
    if (ts.isBinaryExpression(n) && n.operatorToken.kind === ts.SyntaxKind.EqualsToken && ts.isIdentifier(n.left))
      assigned.add(n.left.text);
    return n.forEachChild(visit);
  };
  visit(tree);
  for (const s of tree.statements) {
    if (ts.isFunctionDeclaration(s) && s.name && !assigned.has(s.name.text)) functions.set(s.name.text, s);
    if (ts.isImportDeclaration(s) && !s.attributes && s.importClause?.namedBindings && ts.isNamedImports(s.importClause.namedBindings)) {
      const resolved = resolveSpecifier(path, specifierText(s.moduleSpecifier));
      for (const e of s.importClause.namedBindings.elements)
        if (resolved && !e.isTypeOnly) imports.set(e.name.text, { module: resolved.module, name: e.propertyName?.text ?? e.name.text });
    }
  }
  return { functions, imports };
};
// A function of the contract: its value over the tag, the helpers it reads,
// the bindings it resolves. `role` is what its parameter holds: the node
// (`node`), its tag as a family helper (`family`), or a public tag value
// (`public`, equalities alone).
const analyze = (path: string, f: ts.FunctionDeclaration, role: "node" | "family" | "public",
    helpers: Map<string, Helper>, edges: Map<string, Edge>, depth: number): Value => {
  if (depth > 32) refuse("a helper graph too deep or cyclic");
  const tree = moduleOf(path);
  const name = f.name?.text ?? "";
  if (f.asteriskToken || f.modifiers?.some((m) => m.kind === ts.SyntaxKind.AsyncKeyword)) refuse(`${name} is a generator or async`);
  if (f.parameters.length !== 1) refuse(`${name} takes ${f.parameters.length} parameters`);
  const [p] = f.parameters;
  if (!p || !ts.isIdentifier(p.name) || p.initializer || p.dotDotDotToken || p.questionToken) refuse(`${name}'s parameter is not plain`);
  const x = p && ts.isIdentifier(p.name) ? p.name.text : "";
  const body = f.body ?? refuse(`${name} has no body`);
  const reads = (n: ts.Node): undefined => {
    if (n.kind === ts.SyntaxKind.ThisKeyword || (ts.isIdentifier(n) && n.text === "arguments")) refuse(`${name} reads this or arguments`);
    return n.forEachChild(reads);
  };
  reads(body);
  const { functions, imports } = bindings(path);
  let local: string | null = null;
  // An operand: the tag, the parameter (a tag), the local holding the tag, or a constant.
  const operand = (e: ts.Expression): Value => {
    while (ts.isParenthesizedExpression(e)) e = e.expression;
    if (role === "node" && ts.isPropertyAccessExpression(e) && ts.isIdentifier(e.expression) && e.expression.text === x &&
        e.name.text === "kind") return (t) => t;
    if (role !== "node" && ts.isIdentifier(e) && e.text === x) return (t) => t;
    if (local !== null && ts.isIdentifier(e) && e.text === local) return (t) => t;
    if (ts.isPropertyAccessExpression(e) && ts.isIdentifier(e.expression) && e.expression.text === "SyntaxKind") {
      const bound = imports.get("SyntaxKind") ?? refuse(`${name} reads a SyntaxKind no import binds`);
      edges.set(`${path}#SyntaxKind`, [path, "SyntaxKind", bound.module, bound.name]);
    }
    const c = constant(tree, e, edges);
    if (c !== null) return () => c;
    return refuse(`${name} reads ${e.getText(tree)}`);
  };
  const condition = (e: ts.Expression): Value => {
    while (ts.isParenthesizedExpression(e)) e = e.expression;
    if (ts.isBinaryExpression(e)) {
      const op = e.operatorToken.kind;
      if (op === ts.SyntaxKind.BarBarToken || op === ts.SyntaxKind.AmpersandAmpersandToken) {
        const l = condition(e.left), r = condition(e.right);
        return op === ts.SyntaxKind.BarBarToken ? (t) => l(t) === true || r(t) === true : (t) => l(t) === true && r(t) === true;
      }
      if (op === ts.SyntaxKind.EqualsEqualsEqualsToken) {
        const l = operand(e.left), r = operand(e.right);
        return (t) => l(t) === r(t);
      }
      if (op === ts.SyntaxKind.GreaterThanEqualsToken || op === ts.SyntaxKind.LessThanEqualsToken) {
        if (role === "public") refuse(`${name}, a tag guard a program may call, tests a range`);
        const l = operand(e.left), r = operand(e.right);
        return op === ts.SyntaxKind.GreaterThanEqualsToken ? (t) => Number(l(t)) >= Number(r(t)) : (t) => Number(l(t)) <= Number(r(t));
      }
    }
    if (ts.isCallExpression(e) && ts.isIdentifier(e.expression) && e.arguments.length === 1) {
      const [arg] = e.arguments;
      const callee = e.expression.text;
      const declaredHere = functions.get(callee);
      const importedFrom = imports.get(callee);
      let helperPath = path;
      let helper = declaredHere;
      let helperName = callee;
      if (!helper && importedFrom) {
        helper = bindings(importedFrom.module).functions.get(importedFrom.name);
        helperPath = importedFrom.module;
        helperName = importedFrom.name;
        edges.set(`${path}#${callee}`, [path, callee, importedFrom.module, importedFrom.name]);
      }
      if (!helper) return refuse(`${name} calls ${callee}, no stable function of the package`);
      if (!arg) return refuse(`${name} calls ${callee} without an argument`);
      // The helper's domain: the node itself, or its tag.
      const onNode = role === "node" && ts.isIdentifier(arg) && arg.text === x;
      const argument = onNode ? null : operand(arg);
      const helperRole = onNode ? "node" : role === "public" ? "public" : "family";
      const v = analyze(helperPath, helper, helperRole, helpers, edges, depth + 1);
      helpers.set(`${helperPath}#${helperName}`, { key: `${helperPath}#${helperName}`, text: textOf(helperPath, helper) });
      return onNode || !argument ? v : (t) => v(Number(argument(t)));
    }
    return refuse(`${name} tests ${e.getText(tree)}`);
  };
  const statements = body.statements;
  const [first, second] = statements;
  if (statements.length === 1 && first && ts.isReturnStatement(first) && first.expression) return condition(first.expression);
  if (statements.length === 2 && first && second && ts.isVariableStatement(first) && ts.isReturnStatement(second) &&
      second.expression && first.declarationList.flags & ts.NodeFlags.Const) {
    const [d] = first.declarationList.declarations;
    if (!d || first.declarationList.declarations.length !== 1 || !ts.isIdentifier(d.name) || !d.initializer)
      return refuse(`${name} declares more than its tag`);
    const tag = operand(d.initializer);
    local = d.name.text;
    const c = condition(second.expression);
    return (t) => c(Number(tag(t)));
  }
  if (statements.length === 1 && first && ts.isSwitchStatement(first)) {
    const subject = operand(first.expression);
    const cases: number[] = [];
    let sawDefault = false;
    for (const clause of first.caseBlock.clauses) {
      if (ts.isDefaultClause(clause)) {
        const [r] = clause.statements;
        if (clause.statements.length !== 1 || !r || !ts.isReturnStatement(r) || r.expression?.kind !== ts.SyntaxKind.FalseKeyword)
          refuse(`${name}'s default returns other than false`);
        sawDefault = true;
        continue;
      }
      // A case label is a constant, its enum binding recorded as an operand's.
      operand(clause.expression);
      cases.push(constant(tree, clause.expression, edges) ?? refuse(`${name} has a case that is no constant`));
      if (clause.statements.length) {
        const [r] = clause.statements;
        if (clause.statements.length !== 1 || !r || !ts.isReturnStatement(r) || r.expression?.kind !== ts.SyntaxKind.TrueKeyword)
          refuse(`${name}'s case returns other than true`);
      }
    }
    if (!sawDefault) refuse(`${name}'s switch has no default`);
    return (t) => cases.includes(Number(subject(t)));
  }
  return refuse(`${name}'s body is outside the contract`);
};
const textOf = (path: string, f: ts.FunctionDeclaration): string => f.getText(moduleOf(path)).trim();

type Entry = { name: string; kind: "node" | "tag"; domain: string; tags: string[]; module: string;
  text: string; helpers: string[]; edges: Edge[] };
const entries: Entry[] = [];
const excluded: [string, string][] = [];
const helperTexts = new Map<string, string>();
for (const [name, { domain, tagged }] of [...declared].sort(([a], [b]) => a < b ? -1 : a > b ? 1 : 0)) {
  const located = chains.get(name);
  if (!located) { excluded.push([name, "no export of the entry point"]); continue; }
  const f = bindings(located.module).functions.get(name);
  if (!f) { excluded.push([name, "no stable function declaration"]); continue; }
  const helpers = new Map<string, Helper>();
  const edges = new Map<string, Edge>();
  try {
    const value = analyze(located.module, f, tagged ? "public" : "node", helpers, edges, 0);
    const tags = values.filter((t) => value(t) === true).map(nameOf);
    for (const h of helpers.values()) helperTexts.set(h.key, h.text);
    entries.push({ name, kind: tagged ? "tag" : "node", domain, tags, module: located.module,
      text: textOf(located.module, f), helpers: [...helpers.keys()].sort(),
      edges: [...edges].sort(([a], [b]) => a < b ? -1 : a > b ? 1 : 0).map(([, e]) => e) });
  } catch (error) {
    if (!(error instanceof Refused)) throw error;
    excluded.push([name, error.message]);
  }
}
const closure = guardClosure(entryFile, path => readFileSync(join(root, path)),
  path => moduleOf(path), (from, specifier) => resolveSpecifier(from, specifier)?.module ?? null);
if (!closure) throw Error("the executable closure contains an unrecordable loading form");
closeParser();

const json = (v: unknown): string => JSON.stringify(v) ?? "";
const text = `// Generated by dev/guard-table.mts from the audited installation; reviewed.
// The compiler API's guard table (HOST-FAMILIES.md, "The guard table"):
// each guard's export, kind, domain and exact tag set, its function's text
// and resolution, and the helpers and bindings it reads.
import type { GuardTable } from "./host-families.mts";

export const compilerApiGuards: GuardTable = {
  entryPoint: ${json(entryPoint)},
  conditions: ${json(conditions)},
  entryModule: ${json(relative(root, join(root, entryFile)))},
  closure: ${json(closure)},
  helpers: {
${[...helperTexts].sort(([a], [b]) => a < b ? -1 : 1).map(([k, t]) => `    ${json(k)}: ${json(t)},`).join("\n")}
  },
  guards: [
${entries.map((e) => `    { name: ${json(e.name)}, kind: ${json(e.kind)}, domain: ${json(e.domain)}, tags: ${json(e.tags)},
      module: ${json(e.module)}, helpers: ${json(e.helpers)}, edges: ${json(e.edges)},
      text: ${json(e.text)} },`).join("\n")}
  ],
  excluded: [
${excluded.map(([n, why]) => `    [${json(n)}, ${json(why)}],`).join("\n")}
  ],
};
`;
const out = join(repository, "tools", "compiler-api-guards.mts");
if (process.argv.includes("--check")) {
  let current = "";
  try { current = readFileSync(out, "utf8"); } catch { /* none yet */ }
  if (current !== text) {
    process.stderr.write("the guard table differs from the generator's output: node dev/guard-table.mts > tools/compiler-api-guards.mts\n");
    process.exitCode = 1;
  } else console.log(`guard table: ${entries.length} guards as generated, ${excluded.length} declared guards excluded`);
} else process.stdout.write(text);
