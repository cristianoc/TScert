// Syntax measurements: node dev/declaration-metrics.mts syntax [source]
// Fixed census inputs: node dev/declaration-metrics.mts inputs <directory>
// One executed parse sample: TSCERT_STAGE_STORE=<fresh directory>
//   node dev/declaration-metrics.mts parse <input directory> <output directory>
// Five-sample median: node dev/declaration-metrics.mts summary <five report.json paths>
// Inputs are prepared once, then used unchanged by both checkouts. The parse
// report retains input hashes, outcomes and every stage's CPU measurements.
import { createHash } from "node:crypto";
import { mkdirSync, readFileSync, readdirSync, writeFileSync } from "node:fs";
import { join, resolve } from "node:path";
import { close, openText } from "../tools/fragment-parse.mts";
import { syntax as ts, nameOf, childOf } from "../tools/syntax.mts";
import { parseSource } from "../pipeline/verify-source.mts";
import { Recorder, storeSetting } from "../pipeline/stages.mts";
import { prepare } from "./census.mts";

type FunctionNode =
  | ts.FunctionDeclaration
  | ts.FunctionExpression
  | ts.ArrowFunction
  | ts.MethodDeclaration
  | ts.ConstructorDeclaration
  | ts.GetAccessorDeclaration
  | ts.SetAccessorDeclaration;
function isFunction(node: ts.Node): node is FunctionNode {
  return (
    ts.isFunctionDeclaration(node) ||
    ts.isFunctionExpression(node) ||
    ts.isArrowFunction(node) ||
    ts.isMethodDeclaration(node) ||
    ts.isConstructorDeclaration(node) ||
    ts.isGetAccessorDeclaration(node) ||
    ts.isSetAccessorDeclaration(node)
  );
}
type Scope = {
  parent: Scope | null;
  owner: FunctionNode | null;
  bindings: Map<string, Binding>;
};
type Binding = {
  name: string;
  node: ts.Identifier;
  scope: Scope;
  mutable: boolean;
  kind: "parameter" | "variable" | "function";
  captures: Set<FunctionNode>;
};
const hash = (text: string | Buffer): string =>
  createHash("sha256").update(text).digest("hex");

/** Lexical bindings are resolved from innermost scope; property names and
 * type syntax do not count as value references. Captures are direct uses in
 * a function's own body, rather than uses in its nested functions. Mutable
 * means a let/var binding or a parameter, regardless of observed assignment;
 * const bindings to mutable objects are reported separately on mutation. */
function syntaxMetrics(path: string): object {
  const text = readFileSync(path, "utf8");
  const tree = openText(path, text);
  const collector = tree.statements.find(
    (n): n is ts.FunctionDeclaration =>
      ts.isFunctionDeclaration(n) && n.name?.text === "collectDeclarations",
  );
  if (!collector?.body) throw Error("collectDeclarations has no body");
  const line = (n: ts.Node): number =>
    tree.getLineAndCharacterOfPosition(n.getStart(tree)).line + 1;
  const location = (n: ts.Node): string => {
    const at = tree.getLineAndCharacterOfPosition(n.getStart(tree));
    return `${at.line + 1}:${at.character + 1}`;
  };
  const label = (n: FunctionNode): string => {
    const own = nameOf(n);
    const p = n.parent;
    const name =
      own && ts.isIdentifier(own)
        ? own.text
        : p && ts.isVariableDeclaration(p) && ts.isIdentifier(p.name)
          ? p.name.text
          : ts.SyntaxKind[n.kind];
    return `${name}:${location(n)}`;
  };
  const root: Scope = { parent: null, owner: null, bindings: new Map() };
  const scopes = new Map<ts.Node, Scope>();
  const bindings: Binding[] = [];
  const functions: FunctionNode[] = [];
  const names = new Set<ts.Node>();
  const bind = (
    name: ts.BindingName,
    scope: Scope,
    mutable: boolean,
    kind: Binding["kind"] = "variable",
  ): void => {
    if (ts.isIdentifier(name)) {
      const binding: Binding = {
        name: name.text,
        node: name,
        scope,
        mutable,
        kind,
        captures: new Set(),
      };
      scope.bindings.set(name.text, binding);
      bindings.push(binding);
      names.add(name);
    } else
      for (const element of name.elements)
        if (ts.isBindingElement(element) && element.name)
          bind(element.name, scope, mutable, kind);
  };
  const declare = (node: ts.Node, enclosing: Scope): void => {
    if (ts.isFunctionDeclaration(node) && node.name)
      bind(node.name, enclosing, false, "function");
    let scope = enclosing;
    if (
      isFunction(node) ||
      ts.isBlock(node) ||
      ts.isCatchClause(node) ||
      ts.isForStatement(node) ||
      ts.isForOfStatement(node) ||
      ts.isForInStatement(node) ||
      ts.isCaseBlock(node)
    ) {
      scope = {
        parent: enclosing,
        owner: isFunction(node) ? node : enclosing.owner,
        bindings: new Map(),
      };
    }
    scopes.set(node, scope);
    if (isFunction(node)) {
      functions.push(node);
      if (ts.isFunctionExpression(node) && node.name)
        bind(node.name, scope, false, "function");
      for (const p of node.parameters)
        if (p.name) bind(p.name, scope, true, "parameter");
    }
    if (ts.isVariableDeclaration(node)) {
      let target = scope;
      const list = node.parent;
      const lexical =
        ts.isCatchClause(list) ||
        (ts.isVariableDeclarationList(list) &&
          !!(list.flags & (ts.NodeFlags.Let | ts.NodeFlags.Const)));
      if (!lexical)
        while (target.parent && target.parent.owner === target.owner)
          target = target.parent;
      bind(
        node.name,
        target,
        !ts.isVariableDeclarationList(list) ||
          !(list.flags & ts.NodeFlags.Const),
      );
    }
    node.forEachChild((child) => declare(child, scope));
  };
  declare(collector, root);
  const mutations = new Set<Binding>();
  const resolveBinding = (id: ts.Identifier): Binding | undefined => {
    for (let scope = scopes.get(id); scope; scope = scope.parent ?? undefined) {
      const binding = scope.bindings.get(id.text);
      if (binding) return binding;
    }
    return undefined;
  };
  const reference = (node: ts.Node): void => {
    if (ts.isTypeNode(node)) return;
    if (ts.isIdentifier(node) && !names.has(node)) {
      const p = node.parent;
      const property =
        (ts.isPropertyAccessExpression(p) && p.name === node) ||
        (ts.isBindingElement(p) && p.propertyName === node) ||
        ((ts.isLabeledStatement(p) ||
          ts.isBreakStatement(p) ||
          ts.isContinueStatement(p)) &&
          p.label === node) ||
        ((ts.isPropertyAssignment(p) ||
          ts.isMethodDeclaration(p) ||
          ts.isPropertyDeclaration(p)) &&
          p.name === node &&
          !ts.isComputedPropertyName(p.name));
      if (!property) {
        const binding = resolveBinding(node);
        const owner = scopes.get(node)?.owner;
        if (
          binding &&
          owner &&
          owner !== collector &&
          binding.scope.owner !== owner
        )
          binding.captures.add(owner);
        // Syntactic mutation of const-held storage: property/element writes
        // and calls of the standard Array/Map/Set mutator names. Aliases and
        // mutations inside called functions are outside this measurement.
        if (
          binding &&
          (ts.isPropertyAccessExpression(p) ||
            ts.isElementAccessExpression(p)) &&
          p.expression === node
        ) {
          const outer = p.parent;
          if (
            (ts.isBinaryExpression(outer) &&
              outer.left === p &&
              outer.operatorToken.kind >= ts.SyntaxKind.FirstAssignment &&
              outer.operatorToken.kind <= ts.SyntaxKind.LastAssignment) ||
            ((ts.isPostfixUnaryExpression(outer) ||
              ts.isPrefixUnaryExpression(outer)) &&
              (outer.operator === ts.SyntaxKind.PlusPlusToken ||
                outer.operator === ts.SyntaxKind.MinusMinusToken)) ||
            ts.isDeleteExpression(outer) ||
            (ts.isCallExpression(outer) &&
              outer.expression === p &&
              ts.isPropertyAccessExpression(p) &&
              [
                "set",
                "add",
                "delete",
                "clear",
                "push",
                "pop",
                "shift",
                "unshift",
                "splice",
                "sort",
                "reverse",
                "fill",
                "copyWithin",
              ].includes(p.name.text))
          )
            mutations.add(binding);
        }
      }
    }
    node.forEachChild(reference);
  };
  reference(collector);
  const captured = (binding: Binding): object => ({
    name: binding.name,
    line: line(binding.node),
    kind: binding.kind,
    column:
      tree.getLineAndCharacterOfPosition(binding.node.getStart(tree))
        .character + 1,
    closures: [...binding.captures].map(label),
    count: binding.captures.size,
  });
  const inner = functions.filter((n) => n !== collector);
  const options = collector.parameters.find(
    (p) => ts.isIdentifier(p.name) && p.name.text === "options",
  );
  const interfaceMembers = (name: string): readonly ts.TypeElement[] => {
    const declaration = tree.statements.find(
      (s): s is ts.InterfaceDeclaration =>
        ts.isInterfaceDeclaration(s) && s.name.text === name,
    );
    if (!declaration) throw Error(`option interface missing: ${name}`);
    return [
      ...(declaration.heritageClauses ?? []).flatMap((clause) =>
        clause.types.flatMap((base) => interfaceMembers(base.expression.getText(tree))),
      ),
      ...declaration.members,
    ];
  };
  const optionMembers = options?.type && ts.isTypeLiteralNode(options.type)
    ? options.type.members
    : options?.type && ts.isTypeReferenceNode(options.type)
      ? interfaceMembers(options.type.typeName.getText(tree))
      : null;
  if (!optionMembers) throw Error("options is not a type literal or named interface");
  const topLevel: FunctionNode[] = [];
  for (const statement of tree.statements) {
    if (ts.isFunctionDeclaration(statement) && statement.body)
      topLevel.push(statement);
    if (ts.isVariableStatement(statement))
      for (const declaration of statement.declarationList.declarations)
        if (declaration.initializer && isFunction(declaration.initializer))
          topLevel.push(declaration.initializer);
  }
  return {
    file: path,
    sha256: hash(text),
    collectDeclarations: {
      startLine: line(collector),
      endLine: tree.getLineAndCharacterOfPosition(collector.end - 1).line + 1,
      lines:
        tree.getLineAndCharacterOfPosition(collector.end - 1).line +
        2 -
        line(collector),
      innerFunctions: inner.map((n) => ({
        name: label(n),
        kind: ts.SyntaxKind[n.kind],
        start: n.getStart(tree),
        end: n.end,
        captures: bindings
          .filter((b) => b.captures.has(n))
          .map((b) => `${b.name}:${location(b.node)}`),
      })),
      innerFunctionCount: inner.length,
      closureCount: inner.filter((n) => bindings.some((b) => b.captures.has(n)))
        .length,
      mutableBindings: bindings
        .filter((b) => b.mutable && b.captures.size)
        .map(captured),
      mutatedConstStorage: bindings
        .filter((b) => !b.mutable && mutations.has(b) && b.captures.size)
        .map(captured),
      options: optionMembers.map((m) => ({
        name: nameOf(m)?.getText(tree),
        optional: !!childOf(m, "questionToken"),
        type: childOf(m, "type")?.getText(tree),
      })),
      optionsCount: optionMembers.length,
    },
    topLevelFunctions: topLevel.map(label),
    topLevelFunctionCount: topLevel.length,
    topLevelFunctionDeclarations: topLevel
      .filter(ts.isFunctionDeclaration)
      .map(label),
  };
}

/** The collector's census sources and its direct caller, each parsed whole
 * as the census parses it. */
const measuredFiles = ["declaration-graph.mts", "fragment-parse.mts"];
function inputs(directory: string): void {
  mkdirSync(directory, { recursive: true });
  if (readdirSync(directory).length)
    throw Error("inputs requires an empty directory");
  prepare(directory, "tools");
  const manifest = measuredFiles.map((file) => ({
    file,
    sha256: hash(readFileSync(join(directory, "tools", file))),
  }));
  writeFileSync(
    join(directory, "inputs.json"),
    JSON.stringify(manifest, null, 2) + "\n",
  );
  writeFileSync(join(directory, "sources.json"), sourceManifest(directory));
}

/** Every fixed source/configuration file, including the local import closure.
 * Installed packages are supplied by prepare's node_modules link. */
function sourceManifest(directory: string): string {
  const files: { file: string; sha256: string }[] = [];
  const visit = (relative: string): void => {
    for (const entry of readdirSync(join(directory, relative), {
      withFileTypes: true,
    }).sort((a, b) => a.name.localeCompare(b.name))) {
      const file = join(relative, entry.name);
      if (entry.name === "node_modules" || file === "sources.json") continue;
      if (entry.isDirectory()) visit(file);
      else if (entry.isFile())
        files.push({ file, sha256: hash(readFileSync(join(directory, file))) });
    }
  };
  visit("");
  return JSON.stringify(files, null, 2) + "\n";
}

/** A fresh process per sample; parse itself closes its parser per input.
 * Declaration sessions have the lifetime the ordinary parse stage gives them. */
function parse(directory: string, output: string): object {
  const manifest = readFileSync(join(directory, "sources.json"), "utf8");
  if (manifest !== sourceManifest(directory))
    throw Error("fixed input sources differ from sources.json");
  if (!process.env["TSCERT_STAGE_STORE"])
    throw Error("set TSCERT_STAGE_STORE to a fresh directory");
  const setting = storeSetting();
  if (setting.off) throw Error("parse requires an empty stage store directory");
  mkdirSync(setting.directory, { recursive: true });
  if (readdirSync(setting.directory).length)
    throw Error("parse requires an empty stage store directory");
  mkdirSync(output, { recursive: true });
  const recorder = new Recorder(join(output, "invocations.jsonl"));
  const outcomes: {
    file: string;
    sha256: string;
    code: ReturnType<typeof parseSource>["parsed"]["code"];
    detail: string;
  }[] = [];
  for (const file of measuredFiles) {
    const source = join(directory, "tools", file);
    const artifacts = join(output, file);
    mkdirSync(artifacts, { recursive: true });
    const { parsed } = parseSource(
      source,
      join(directory, "tools", "tsconfig.json"),
      artifacts,
      recorder,
    );
    outcomes.push({
      file,
      sha256: hash(readFileSync(source)),
      code: parsed.code,
      detail: parsed.detail,
    });
    if (parsed.detail.includes("did not load a strict tsconfig"))
      throw Error(parsed.detail);
  }
  const parses = recorder.records.filter((r) => r.stage === "parse");
  if (
    parses.length !== outcomes.length ||
    parses.some((r) => r.execution !== "executed" || "unavailable" in r.cpu)
  )
    throw Error("every input must have an executed parse with CPU time");
  const cpuSeconds =
    parses.reduce(
      (sum, r) =>
        sum + ("unavailable" in r.cpu ? 0 : r.cpu.userMs + r.cpu.systemMs),
      0,
    ) / 1000;
  const report = {
    sourceManifestSha256: hash(manifest),
    cpuSeconds,
    parses: parses.length,
    executed: parses.length,
    replayed: 0,
    unavailable: 0,
    outcomes,
  };
  writeFileSync(
    join(output, "report.json"),
    JSON.stringify(report, null, 2) + "\n",
  );
  return report;
}

function summary(paths: string[]): object {
  if (paths.length !== 5) throw Error("summary requires five report paths");
  const samples = paths.map((path) => {
    const report: unknown = JSON.parse(readFileSync(path, "utf8"));
    if (
      typeof report !== "object" ||
      report === null ||
      !("cpuSeconds" in report) ||
      typeof report.cpuSeconds !== "number" ||
      !Number.isFinite(report.cpuSeconds)
    )
      throw Error(`${path}: missing CPU seconds`);
    return report.cpuSeconds;
  });
  return { samples, median: [...samples].sort((a, b) => a - b)[2] };
}

try {
  const [command, first, second] = process.argv.slice(2);
  if (command === "syntax")
    console.log(
      JSON.stringify(
        syntaxMetrics(resolve(first ?? "tools/declaration-graph.mts")),
        null,
        2,
      ),
    );
  else if (command === "inputs" && first) inputs(resolve(first));
  else if (command === "parse" && first && second) {
    const result = parse(resolve(first), resolve(second));
    console.log(JSON.stringify(result, null, 2));
  } else if (command === "summary")
    console.log(JSON.stringify(summary(process.argv.slice(3)), null, 2));
  else
    throw Error(
      "usage: declaration-metrics.mts syntax [source] | inputs <directory> | parse <inputs> <output> | summary <five reports>",
    );
} finally {
  close();
}
