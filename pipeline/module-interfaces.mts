// Component interface orchestration. Only invokeProcess results supply
// interfaces: every replay validates its exact manifest and payload digest.
import { mkdirSync, readFileSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import { canonical, verifierBuild, verifierCall } from "./stage-execution.mts";
import type { Canonical } from "./stage-execution.mts";
import { invokeProcess } from "./stages.mts";
import type { Invoked, InvokeOptions } from "./stages.mts";

/** JSON data carried between audited processes. */
type ObjectWire = { [key: string]: Canonical };
function object(value: Canonical): ObjectWire {
  if (value === null || typeof value !== "object" || Array.isArray(value)) throw Error("expected object");
  return value as ObjectWire; // asserted: Canonical's only non-array object is its record alternative
}
function array(value: Canonical | undefined): readonly Canonical[] {
  if (!Array.isArray(value)) throw Error("expected array");
  return value;
}
function string(value: Canonical | undefined): string {
  if (typeof value !== "string") throw Error("expected string");
  return value;
}
function json(text: string): Canonical {
  const value: unknown = JSON.parse(text);
  function valid(v: unknown): v is Canonical {
    return v === null || typeof v === "string" || typeof v === "boolean" ||
      (typeof v === "number" && Number.isFinite(v)) ||
      (Array.isArray(v) ? v.every(valid) : typeof v === "object" && Object.values(v).every(valid));
  }
  if (!valid(value)) throw Error("invalid JSON value");
  return value;
}
function exact(value: Canonical, fields: readonly string[]): ObjectWire {
  const v = object(value);
  if (Object.keys(v).length !== fields.length || Object.keys(v).some((k) => !fields.includes(k)))
    throw Error(`expected fields ${fields.join(",")}`);
  return v;
}

/** Semantic inputs common to the component checks and their importer. */
export type InterfaceOptions = {
  mode: 8 | 9;
  fuel: number;
  rounds: number;
  force: readonly string[];
  allCuts: boolean;
  given: string;
  work: string;
  invocation: InvokeOptions;
  /** The parser's canonical ModuleAst for an own-file publication. Its
   * location and declaration identities are the imported path's, rather
   * than the own-file snapshot's file key. Supplying it runs its complete
   * component check even when the importer itself selects one function. */
  ownModule?: string;
};
export type PreparedInterfaces = { path: string; records: Invoked[] };

/** Resolve the DAG before any parent's claim. Failures propagate, so no
 * fallback result can be published under the successful component key. */
export function prepareInterfaces(fragmentPath: string, options: InterfaceOptions): PreparedInterfaces {
  mkdirSync(options.work, { recursive: true });
  let ast = object(json(readFileSync(fragmentPath, "utf8")));
  let source = fragmentPath;
  const rawGiven = readFileSync(options.given, "utf8").split("\n").filter((s) => s.trim() !== "").map(json);
  if (options.ownModule !== undefined) {
    const own = object(json(readFileSync(options.ownModule, "utf8")));
    if (own.sourceSha256 !== ast.sourceSha256) throw Error("own module source differs from the checked file");
    const ownLocation = string(own.location);
    ast = { ...ast, modules: [...array(ast.modules).filter((m) => string(object(m).location) !== ownLocation), own] };
    source = join(options.work, "own-fragment.json");
    writeFileSync(source, canonical(ast));
    for (const line of rawGiven) {
      const row = object(line), u = string(row.unit);
      if (!u.startsWith("module:")) row.unit = `module:${ownLocation}#${u}`;
    }
  }
  const given = new Map<string, Canonical>();
  for (const line of rawGiven) {
    const unit = string(object(line).unit);
    const old = given.get(unit);
    if (old !== undefined && canonical(old) !== canonical(line)) throw Error(`conflicting given lines: ${unit}`);
    given.set(unit, line);
  }
  const records: Invoked[] = [];
  const invoke = (args: string[]): Invoked => {
    const run = invokeProcess(verifierCall(verifierBuild, ["--subtype-rounds", String(options.rounds), ...args]),
      { ...options.invocation, reuse: false });
    records.push(run);
    if (run.status !== 0) throw Error(`interface stage ${run.record.execution}: ${run.stderr}`);
    return run;
  };
  const plan = exact(json(invoke(["--module-interface-plan", source]).stdout), ["components"]);
  const byModule = new Map<string, { key: string; interface: Canonical }>();
  const projections: Canonical[] = [];
  for (const [index, raw] of array(plan.components).entries()) {
    const component = exact(raw, ["modules", "dependencies"]);
    const members = array(component.modules).map((m) => string(object(m).location));
    const dependencies: { key: string; interface: Canonical }[] = [];
    for (const location of array(component.dependencies).map(string)) {
      const dependency = byModule.get(location);
      if (dependency === undefined) throw Error(`dependency not established before parent: ${location}`);
      if (!dependencies.includes(dependency)) dependencies.push(dependency);
    }
    const request = { modules: array(component.modules), dependencies,
      given: [...given.entries()].filter(([u]) => members.some((m) => u.startsWith(`module:${m}#`)))
        .sort(([a], [b]) => a < b ? -1 : a > b ? 1 : 0).map(([, v]) => v),
      force: options.force, allCuts: options.allCuts, fuel: options.fuel, mode: options.mode };
    const path = join(options.work, `component-${index}.json`);
    writeFileSync(path, canonical(request));
    const run = invoke(["--module-interface", path]);
    const result = exact(json(run.stdout), ["modules"]);
    // An ineligible execution can be consumed in this invocation; its
    // complete result bytes still bind every parent invocation's input.
    const dependency = { key: run.record.key ?? "executed-without-replay", interface: result };
    for (const location of members) byModule.set(location, dependency);
    projections.push(...array(result.modules));
  }
  const path = join(options.work, "interfaces.json");
  writeFileSync(path, canonical({ modules: projections }));
  return { path, records };
}

/** The importer is one process stage, with every file it reads an explicit
 * input role. Stand-ins are importer-only measurement inputs. */
export function verifyWithInterfaces(fragment: string, key: string, names: string, standins: string,
    options: InterfaceOptions): { run: Invoked; interfaces: PreparedInterfaces } {
  const interfaces = prepareInterfaces(fragment, options);
  let importerInterfaces = interfaces.path;
  if (options.ownModule !== undefined) {
    const locations = array(object(json(readFileSync(fragment, "utf8"))).modules).map((m) => string(object(m).location));
    const modules = array(object(json(readFileSync(interfaces.path, "utf8"))).modules)
      .filter((row) => locations.includes(string(object(object(row).module).location)));
    importerInterfaces = join(options.work, "importer-interfaces.json");
    writeFileSync(importerInterfaces, canonical({ modules }));
  }
  const environment: Record<string, string> = {};
  if (options.force.length > 0) environment.TSCERT_FORCE = options.force.join(",");
  if (options.allCuts) environment.TSCERT_ALL_CUTS = "1";
  const run = invokeProcess(verifierCall(verifierBuild, ["--subtype-rounds", String(options.rounds),
    "--verify-interface-stage", String(options.mode), fragment, importerInterfaces, options.given, standins,
    key, String(options.fuel), names], environment), { ...options.invocation, reuse: false });
  return { run, interfaces };
}
