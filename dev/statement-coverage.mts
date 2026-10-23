// Statement coverage of a census (docs/DESIGN.md, "Statement coverage"): the
// executable source statements of a directory's modules, each owned by the
// function whose body holds it, and each classified by the census outcome of
// its top-level function's slice. Verified coverage is 100·V/N over the units
// of the census's functions, counts summed before any percentage.
import { syntax as ts, childrenOf, nameOf } from "../tools/syntax.mts";

/** Where a unit's owner lies relative to the census: a function the census
 * slices, module-level code, or a function the census does not slice (a
 * class member, a function a module binding holds). */
export type UnitScope = "census" | "module" | "outside";

/** One executable statement of a source file. */
export type Unit = {
  file: string;
  /** The top-level function owning the unit: a census function's name, a
   * function outside the census's scope, or `<module>`. */
  fn: string;
  /** The nested function holding the unit, by its name and line, or null in
   * the top-level body itself. */
  inner: string | null;
  scope: UnitScope;
  /** The statement's syntax kind; `ExpressionBody` for the synthetic return
   * of an expression-bodied arrow. */
  kind: string;
  /** The statement's span, from its first token, and its position, 1-based. */
  start: number;
  end: number;
  line: number;
  column: number;
};

/** A unit's class: verified, the census outcome of its function's slice
 * where that slice did not verify, `out of scope` for module code and
 * functions the census does not slice, and `not run` for a census function
 * no slice of the record covers. */
export type UnitClass = string;
export const verifiedClass = "verified";
export const outOfScope = "out of scope";
export const notRun = "not run";

/** The census outcome a slice's record gives: what classifies its units. */
export type SliceOutcome = { file: string; fn: string; status: string; phase: string; detail: string };

/** A classified unit, as the census record holds it. */
export type UnitRecord = Unit & { class: UnitClass };

const has = (node: ts.Node, modifier: ts.SyntaxKind): boolean =>
  childrenOf(node, "modifiers").some((m) => m.kind === modifier);

/** The statements that execute, by the name a unit records. Blocks and
 * labels only structure, and imports, exports of bindings, function
 * declarations and type-only declarations run nothing where they stand. */
const executing: ReadonlyMap<ts.SyntaxKind, string> = new Map([
  [ts.SyntaxKind.VariableStatement, "VariableStatement"],
  [ts.SyntaxKind.ExpressionStatement, "ExpressionStatement"],
  [ts.SyntaxKind.IfStatement, "IfStatement"],
  [ts.SyntaxKind.DoStatement, "DoStatement"],
  [ts.SyntaxKind.WhileStatement, "WhileStatement"],
  [ts.SyntaxKind.ForStatement, "ForStatement"],
  [ts.SyntaxKind.ForInStatement, "ForInStatement"],
  [ts.SyntaxKind.ForOfStatement, "ForOfStatement"],
  [ts.SyntaxKind.ContinueStatement, "ContinueStatement"],
  [ts.SyntaxKind.BreakStatement, "BreakStatement"],
  [ts.SyntaxKind.ReturnStatement, "ReturnStatement"],
  [ts.SyntaxKind.WithStatement, "WithStatement"],
  [ts.SyntaxKind.SwitchStatement, "SwitchStatement"],
  [ts.SyntaxKind.ThrowStatement, "ThrowStatement"],
  [ts.SyntaxKind.TryStatement, "TryStatement"],
  [ts.SyntaxKind.DebuggerStatement, "DebuggerStatement"],
  [ts.SyntaxKind.ExportAssignment, "ExportAssignment"],
  [ts.SyntaxKind.ClassDeclaration, "ClassDeclaration"],
  [ts.SyntaxKind.EnumDeclaration, "EnumDeclaration"],
]);

/** The unit kind of a statement that executes; null for any other node, an
 * ambient declaration and a `const enum`. */
function unitKind(node: ts.Node): string | null {
  if (has(node, ts.SyntaxKind.DeclareKeyword)) return null;
  if (ts.isEnumDeclaration(node) && has(node, ts.SyntaxKind.ConstKeyword)) return null;
  return executing.get(node.kind) ?? null;
}

/** The body of a function-like node, where it has one. */
function bodyOf(node: ts.Node): ts.Node | undefined {
  if (ts.isArrowFunction(node) || ts.isFunctionExpression(node) || ts.isClassStaticBlockDeclaration(node))
    return node.body;
  if (ts.isFunctionDeclaration(node) || ts.isMethodDeclaration(node) || ts.isConstructorDeclaration(node) ||
      ts.isGetAccessorDeclaration(node) || ts.isSetAccessorDeclaration(node))
    return node.body;
  return undefined;
}

/** The name a function is known by: its own, the binding or property it
 * initializes, or its kind. */
function functionName(node: ts.Node): string {
  const own = nameOf(node);
  if (own && ts.isIdentifier(own)) return own.text;
  if (ts.isConstructorDeclaration(node)) return "constructor";
  if (ts.isClassStaticBlockDeclaration(node)) return "static";
  const parent = node.parent;
  if (parent && (ts.isVariableDeclaration(parent) || ts.isPropertyAssignment(parent) ||
      ts.isPropertyDeclaration(parent)) && ts.isIdentifier(parent.name))
    return parent.name.text;
  return ts.isArrowFunction(node) ? "<arrow>" : "<function>";
}

/** The units of one module, in source order. A top-level function
 * declaration with a name and a body is a census function, as the census
 * slices it; a nested function's units belong to its top-level function,
 * marked with the nested function; a class's members and its field
 * initializers belong to `Class.member` and `Class`. */
export function inventory(file: string, tree: ts.SourceFile): Unit[] {
  const units: Unit[] = [];
  const position = (at: number): { line: number; column: number } => {
    const p = tree.getLineAndCharacterOfPosition(at);
    return { line: p.line + 1, column: p.character + 1 };
  };
  const add = (node: ts.Node, kind: string, fn: string, inner: string | null, scope: UnitScope): void => {
    const start = node.getStart(tree);
    units.push({ file, fn, inner, scope, kind, start, end: node.end, ...position(start) });
  };
  type Owner = { fn: string; inner: string | null; scope: UnitScope };
  const visit = (node: ts.Node, owner: Owner, top: boolean): void => {
    if (ts.isInterfaceDeclaration(node) || ts.isTypeAliasDeclaration(node) || ts.isModuleDeclaration(node) ||
        ts.isImportDeclaration(node) || has(node, ts.SyntaxKind.DeclareKeyword))
      return;
    const body = bodyOf(node);
    if (body) {
      const name = functionName(node);
      const label = `${name}:${position(node.getStart(tree)).line}`;
      const inner: Owner = top && ts.isFunctionDeclaration(node) && node.name
        ? { fn: node.name.text, inner: null, scope: "census" }
        : owner.scope === "module" ? { fn: classMember(node, name.startsWith("<") ? label : name), inner: null,
            scope: "outside" }
        : { fn: owner.fn, inner: label, scope: owner.scope };
      if (!ts.isBlock(body)) add(body, "ExpressionBody", inner.fn, inner.inner, inner.scope);
      node.forEachChild((child) => visit(child, inner, false));
      return;
    }
    if (ts.isPropertyDeclaration(node) && node.initializer) {
      const field: Owner = owner.scope === "module" ? { fn: classMember(node, ""), inner: null, scope: "outside" }
        : owner;
      add(node, "PropertyDeclaration", field.fn, field.inner, field.scope);
      node.forEachChild((child) => visit(child, field, false));
      return;
    }
    const kind = unitKind(node);
    if (kind) add(node, kind, owner.fn, owner.inner, owner.scope);
    node.forEachChild((child) => visit(child, owner, false));
  };
  const module: Owner = { fn: "<module>", inner: null, scope: "module" };
  for (const s of tree.statements) visit(s, module, true);
  return units.sort((a, b) => a.start - b.start);
}

/** A class member's owner name, `Class.member`, or `Class` for a field
 * initializer; the function's own name elsewhere. */
function classMember(node: ts.Node, name: string): string {
  const parent = node.parent;
  if (parent && (ts.isClassDeclaration(parent) || ts.isClassExpression(parent))) {
    const cls = parent.name ? parent.name.text : "<class>";
    return name === "" ? cls : `${cls}.${name}`;
  }
  return name === "" ? "<module>" : name;
}

const isTimeout = (s: SliceOutcome): boolean => s.detail.startsWith("timeout:");

/** A unit's class, by its function's slice among `slices` (keyed
 * `file#fn`). */
export function classify(unit: Unit, slices: ReadonlyMap<string, SliceOutcome>): UnitClass {
  if (unit.scope !== "census") return outOfScope;
  const s = slices.get(`${unit.file}#${unit.fn}`);
  if (!s) return notRun;
  if (s.status === "verified") return verifiedClass;
  return isTimeout(s) ? "timeout" : `${s.status}/${s.phase}`;
}

// ---------------------------------------------------------------------------
// Counts and their report

type Counts = { v: number; n: number; classes: Map<UnitClass, number> };
const emptyCounts = (): Counts =>
  ({ v: 0, n: 0, classes: new Map() });

function count(into: Counts, u: UnitRecord): void {
  into.classes.set(u.class, (into.classes.get(u.class) ?? 0) + 1);
  if (u.scope !== "census" || u.class === notRun) return;
  into.n++;
  if (u.class === verifiedClass) into.v++;
}

/** 100·V/N to one decimal, `n/a` for N = 0. */
const percent = (v: number, n: number): string => (n === 0 ? "n/a" : `${((100 * v) / n).toFixed(1)}%`);

/** The coverage line of a set of counts, with its functions' count. */
function line(c: Counts, functions: { verified: number; all: number }): string {
  return `${percent(c.v, c.n).padStart(6)}  ${String(c.v).padStart(5)} of ${String(c.n).padEnd(5)} statements · ` +
    `functions ${functions.verified} of ${functions.all} verified`;
}

/** The verified coverage of `units` for the directory, per file and, with
 * `perFunction`, per function. `slices` gives the function counts, which
 * include functions whose body holds no unit. */
export function coverageReport(directory: string, units: readonly UnitRecord[],
    slices: ReadonlyMap<string, SliceOutcome>, perFunction: boolean): string {
  const out: string[] = [];
  const all = emptyCounts();
  const byFile = new Map<string, Counts>();
  const byFunction = new Map<string, Counts>();
  for (const u of units) {
    count(all, u);
    const f = byFile.get(u.file) ?? emptyCounts();
    byFile.set(u.file, f);
    count(f, u);
    if (u.scope === "census") {
      const g = byFunction.get(`${u.file}#${u.fn}`) ?? emptyCounts();
      byFunction.set(`${u.file}#${u.fn}`, g);
      count(g, u);
    }
  }
  const functionsOf = (file: string | null): { verified: number; all: number } => {
    const run = [...slices.values()].filter((s) => file === null || s.file === file);
    return { verified: run.filter((s) => s.status === "verified").length, all: run.length };
  };
  out.push(`top-level-function-body coverage of ${directory}/ (verified statements of the census's functions):`);
  out.push(`  ${line(all, functionsOf(null))}`);
  const notVerified = [...all.classes].filter(([k]) => k !== verifiedClass && k !== outOfScope && k !== notRun)
    .sort((a, b) => b[1] - a[1]);
  out.push(`  not verified, by the slice's outcome: ${notVerified.map(([k, n]) => `${k} ${n}`).join(", ") || "none"}`);
  const outside = units.filter((u) => u.class === outOfScope);
  out.push(`  outside the census's scope, not counted: ${outside.filter((u) => u.scope === "module").length} ` +
    `module statements, ${outside.filter((u) => u.scope === "outside").length} statements of ` +
    `${new Set(outside.filter((u) => u.scope === "outside").map((u) => `${u.file}#${u.fn}`)).size} other functions`);
  const unrun = units.filter((u) => u.class === notRun);
  if (unrun.length)
    out.push(`  census functions no slice of the record covers, not counted: ${unrun.length} statements of ` +
      `${new Set(unrun.map((u) => `${u.file}#${u.fn}`)).size} functions`);
  out.push("per file:");
  const width = Math.max(0, ...[...byFile.keys()].map((k) => k.length));
  for (const [file, c] of [...byFile].sort((a, b) => a[0].localeCompare(b[0])))
    out.push(`  ${file.padEnd(width)} ${line(c, functionsOf(file))}`);
  if (perFunction) {
    out.push("per function:");
    const fwidth = Math.max(0, ...[...byFunction.keys()].map((k) => k.length));
    for (const [key, c] of [...byFunction].sort((a, b) => a[0].localeCompare(b[0]))) {
      const [cls, units] = [...c.classes][0] ?? ["", 0];
      out.push(`  ${key.padEnd(fwidth)} ` + (cls === notRun ? `${units} statements, not run`
        : `${percent(c.v, c.n).padStart(6)}  ${String(c.v).padStart(4)} of ${String(c.n).padEnd(4)} ${cls}`));
    }
  }
  return out.join("\n") + "\n";
}

/** Each unit by its identity across two inventories: its file, function,
 * kind and ordinal among the function's units of that kind. */
function matchKeys(units: readonly UnitRecord[]): Map<string, UnitRecord> {
  const ordinals = new Map<string, number>();
  const keys = new Map<string, UnitRecord>();
  for (const u of units) {
    const base = `${u.file}#${u.fn}#${u.kind}`;
    const k = ordinals.get(base) ?? 0;
    ordinals.set(base, k + 1);
    keys.set(`${base}#${k}`, u);
  }
  return keys;
}

/** Three states of a unit for comparison: verified, counted and not
 * verified, or not counted. */
const state = (u: UnitRecord): "V" | "not V" | "uncounted" =>
  u.class === verifiedClass ? "V" : u.scope === "census" && u.class !== notRun ? "not V" : "uncounted";

/** The movement of verified coverage between two classified inventories:
 * the headline before and after, transitions on matched units, and the
 * units of one side only, deleted and added. */
export function coverageComparison(before: readonly UnitRecord[], after: readonly UnitRecord[]): string {
  const total = (units: readonly UnitRecord[]): Counts => {
    const c = emptyCounts();
    for (const u of units) count(c, u);
    return c;
  };
  const [a, b] = [total(before), total(after)];
  const out: string[] = [];
  out.push(`verified statement coverage: ${percent(a.v, a.n)} (${a.v} of ${a.n}) → ${percent(b.v, b.n)} ` +
    `(${b.v} of ${b.n}); denominator ${b.n - a.n >= 0 ? "+" : ""}${b.n - a.n}`);
  const [ka, kb] = [matchKeys(before), matchKeys(after)];
  const transitions = new Map<string, number>();
  for (const [key, u] of ka) {
    const w = kb.get(key);
    if (!w) continue;
    const t = `${state(u)} → ${state(w)}`;
    transitions.set(t, (transitions.get(t) ?? 0) + 1);
  }
  const deleted = [...ka.keys()].filter((k) => !kb.has(k)).length;
  const added = [...kb.keys()].filter((k) => !ka.has(k)).length;
  out.push("matched statements (file, function, kind, ordinal):");
  for (const [t, n] of [...transitions].sort()) out.push(`  ${t.padEnd(24)} ${n}`);
  out.push(`deleted statements: ${deleted}; added statements: ${added}`);
  return out.join("\n") + "\n";
}
