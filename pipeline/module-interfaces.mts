// Component interface orchestration. Only invokeProcess results supply
// interfaces: every replay validates its exact manifest and payload digest.
import { mkdirSync, readFileSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import { canonical, decodeVerdictLine, decodeWorkerPrepared, verifier, verifierCall } from "./stage-execution.mts";
import type { Canonical, WorkerRequest } from "./stage-execution.mts";
import { invokeProcess, invokeWorker } from "./stages.mts";
import type { Invoked, InvokeOptions, WorkerProtocol, WorkerRun } from "./stages.mts";

/** JSON data carried between audited processes. */
type ObjectWire = { [key: string]: Canonical };
function object(value: Canonical): ObjectWire {
  if (value === null || typeof value !== "object" || Array.isArray(value)) throw Error("expected object");
  return value as ObjectWire; // asserted: Canonical's only non-array object is its record alternative
}
const isCanonicalList = (value: Canonical | undefined): value is readonly Canonical[] => Array.isArray(value);
function array(value: Canonical | undefined): readonly Canonical[] {
  if (!isCanonicalList(value)) throw Error("expected array");
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

/** Explicit adversarial proposals in a control’s verifier invocation. */
export const proposalArgs = (force: readonly string[]): string[] => force.length ? ["--force-proposals", force.join(",")] : [];

/** Semantic inputs common to the component checks and their importer. */
export type InterfaceOptions = {
  mode: 8;
  fuel: number;
  rounds: number;
  force: readonly string[];
  work: string;
  invocation: InvokeOptions;
  /** The parser's canonical ModuleAst for an own-file publication. Its
   * location and declaration identities are the imported path's, rather
   * than the own-file snapshot's file key. Supplying it runs its complete
   * component check even when the importer itself selects one function. */
  ownModule?: string;
  /** Importer roots affect discovery only. */
  names?: string;
};
export type PreparedInterfaces = { path: string; records: Invoked[] };

/** Resolve the DAG before any parent's claim. Failures propagate, so no
 * fallback result can be published under the successful component key. */
export function prepareInterfaces(fragmentPath: string, options: InterfaceOptions): PreparedInterfaces {
  mkdirSync(options.work, { recursive: true });
  let source = fragmentPath;
  const ownLocations: string[] = [];
  if (options.ownModule !== undefined) {
    const ast = object(json(readFileSync(fragmentPath, "utf8")));
    const own = object(json(readFileSync(options.ownModule, "utf8")));
    if (own.sourceSha256 !== ast.sourceSha256) throw Error("own module source differs from the checked file");
    const ownLocation = string(own.location);
    ownLocations.push(ownLocation);
    const withOwn = { ...ast, modules: [...array(ast.modules).filter((m) => string(object(m).location) !== ownLocation), own] };
    source = join(options.work, "own-fragment.json");
    writeFileSync(source, canonical(withOwn));
  }
  const records: Invoked[] = [];
  const invoke = (args: string[]): Invoked => {
    const run = invokeProcess(verifierCall(verifier, ["--subtype-rounds", String(options.rounds), ...args]),
      options.invocation);
    records.push(run);
    if (run.status !== 0) throw Error(`interface stage ${run.record.execution}: ${run.stderr}`);
    return run;
  };
  const selection = join(options.work, "selection.json");
  // (the initialization named as the plan's reach names it, `init`)
  writeFileSync(selection, canonical({
    names: options.names ? options.names.split(",").filter(Boolean).map((n) => n === ":init" ? "init" : n) : null,
    imports: [],
    functions: [],
    own: ownLocations,
  }));
  const plan = exact(json(invoke(["--module-interface-plan", source, selection]).stdout), ["components"]);
  const byModule = new Map<string, { key: string; interface: Canonical }>();
  const projections: Canonical[] = [];
  for (const [index, raw] of array(plan.components).entries()) {
    const component = exact(raw, ["modules", "names", "dependencies"]);
    const members = array(component.modules).map((m) => string(object(m).location));
    const dependencies: { key: string; interface: Canonical }[] = [];
    for (const location of array(component.dependencies).map(string)) {
      const dependency = byModule.get(location);
      if (dependency === undefined) throw Error(`dependency not established before parent: ${location}`);
      if (!dependencies.includes(dependency)) dependencies.push(dependency);
    }
    const request = { modules: array(component.modules), names: array(component.names), dependencies,
      force: options.force, fuel: options.fuel, mode: options.mode };
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

/** The file worker's protocol (`WorkerProtocol`): the parts are the units
 * its preparation line names, in order; a request names units, or null for
 * every one; an answer is a unit's verdict line. */
export const fileWorkerProtocol: WorkerProtocol = {
  parts: (prepared: string): string[] => decodeWorkerPrepared(prepared.trim()).selected.map((u) => u.unit),
  request: (parts: readonly string[] | null): string => {
    const request: WorkerRequest = { units: parts };
    return JSON.stringify(request);
  },
  partOf: (answer: string): string => decodeVerdictLine(answer.trim()).unit,
};

/** The interfaces a check reads: those of the modules the units `names`
 * selects reach, each component's check run before its parents'
 * (`prepareInterfaces`), or, for a fragment with no modules, none. A failure
 * of an interface stage (a timeout, a refusal, an operational failure)
 * propagates: no check runs without the interfaces its imports read. */
function interfacesFor(fragment: string, names: string, options: InterfaceOptions,
    hasModules: boolean): PreparedInterfaces {
  if (hasModules || options.ownModule !== undefined) return prepareInterfaces(fragment, { ...options, names });
  mkdirSync(options.work, { recursive: true });
  const path = join(options.work, "interfaces.json");
  writeFileSync(path, canonical({ modules: [] }));
  return { path, records: [] };
}

const fragmentHasModules = (fragment: string): boolean =>
  array(object(json(readFileSync(fragment, "utf8"))).modules).length > 0;

/** The importer's check by units: the file worker (`--file-worker 8`) of the
 * units `names` selects (comma-separated, `""` every unit) and those their
 * verdicts rest on, at the module interfaces those units reach
 * (`interfacesFor`), prepared before it. The worker prepares the file once
 * and checks its units one after another, each unit's result an entry of its
 * own and each with its own limit, so a unit over its limit costs only its
 * own verdict and its dependents' (`invokeWorker`). Where the interface
 * stages fail, no unit is checked: the error thrown names that failure, and
 * the file's units have no verdict. */
export function verifyByUnits(fragment: string, key: string, names: string, options: InterfaceOptions,
    hasModules: boolean = fragmentHasModules(fragment)): WorkerRun {
  mkdirSync(options.work, { recursive: true });
  const environment: Record<string, string> = {};
  if (process.env.TSCERT_PASS_REFUSALS === "raw") environment.TSCERT_PASS_REFUSALS = "raw";
  const diagnosticEnv = process.env.TSCERT_COMPARE || process.env.TSCERT_NODE || process.env.TSCERT_REPEAT ||
    process.env.TSCERT_OBSERVE || process.env.TSCERT_TRACE_PROPOSALS;
  if (!process.env.TSCERT_GROUP_SHADOW && !environment.TSCERT_PASS_REFUSALS && !diagnosticEnv &&
      process.env.TSCERT_GROUP_REPLAY !== "0") environment.TSCERT_SLICE_DRIVER = "1";
  let interfaces: PreparedInterfaces;
  try {
    interfaces = interfacesFor(fragment, names, options, hasModules);
  } catch (error) {
    throw Error(`the module interfaces its imports read were not established: ${
      error instanceof Error ? error.message : String(error)}`);
  }
  return invokeWorker(verifierCall(verifier,
    ["--subtype-rounds", String(options.rounds), ...proposalArgs(options.force), "--file-worker", String(options.mode),
      fragment, interfaces.path, key, String(options.fuel), names], environment), fileWorkerProtocol, options.invocation);
}

/** The importer is one process stage, with every file it reads an explicit
 * input role, at the module interfaces the units `names` selects reach
 * (`interfacesFor`), prepared before it; an own-module publication's
 * importer reads only the interfaces of the fragment's own modules. */
export function verifyWithInterfaces(fragment: string, key: string, names: string,
    options: InterfaceOptions): { run: Invoked; interfaces: PreparedInterfaces } {
  mkdirSync(options.work, { recursive: true });
  const environment: Record<string, string> = {};
  // Raw refusal text is an additional diagnostic on standard error. Key
  // the observation as well, since the store replays that stream.
  if (process.env.TSCERT_PASS_REFUSALS === "raw") environment.TSCERT_PASS_REFUSALS = "raw";
  const interfaces = interfacesFor(fragment, names, options, fragmentHasModules(fragment));
  let importerInterfaces = interfaces.path;
  if (options.ownModule !== undefined) {
    const locations = array(object(json(readFileSync(fragment, "utf8"))).modules).map((m) => string(object(m).location));
    const modules = array(object(json(readFileSync(interfaces.path, "utf8"))).modules)
      .filter((row) => locations.includes(string(object(object(row).module).location)));
    importerInterfaces = join(options.work, "importer-interfaces.json");
    writeFileSync(importerInterfaces, canonical({ modules }));
  }
  const run = invokeProcess(verifierCall(verifier,
    ["--subtype-rounds", String(options.rounds), ...proposalArgs(options.force), "--verify-interface-stage", String(options.mode),
      fragment, importerInterfaces, key, String(options.fuel), names], environment),
    options.invocation);
  return { run, interfaces };
}
