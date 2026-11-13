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
  let ast = object(json(readFileSync(fragmentPath, "utf8")));
  let source = fragmentPath;
  if (options.ownModule !== undefined) {
    const own = object(json(readFileSync(options.ownModule, "utf8")));
    if (own.sourceSha256 !== ast.sourceSha256) throw Error("own module source differs from the checked file");
    const ownLocation = string(own.location);
    ast = { ...ast, modules: [...array(ast.modules).filter((m) => string(object(m).location) !== ownLocation), own] };
    source = join(options.work, "own-fragment.json");
    writeFileSync(source, canonical(ast));
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
    own: options.ownModule === undefined ? [] : [string(object(json(readFileSync(options.ownModule, "utf8"))).location)],
  }));
  const plan = exact(json(invoke(["--module-interface-plan", source, selection]).stdout), ["components"]);
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
    const request = { modules: array(component.modules), dependencies, force: options.force, fuel: options.fuel,
      mode: options.mode };
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

/** The importer's check by units (`invokeWorker`): its worker stage's
 * result, and, where the module interfaces its imports read could not be
 * established, why: the checks are then those at ordinary contracts. */
export type CheckedUnits = { run: WorkerRun; interfaceFailure: string | null };

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

/** The importer's check by units: the file worker (`--file-worker 8`) at
 * its modules' interfaces, or at ordinary contracts where it reads no
 * module, of the units `names` selects (comma-separated, `""` every unit)
 * and those their verdicts rest on. The worker prepares the file once and
 * checks its units one after another, each unit's result an entry of its
 * own and each with its own limit, so a unit over its limit costs only its
 * own verdict and its dependents' (`invokeWorker`). The module interfaces
 * are those the selected units' code reaches. Where the module-interface
 * stages fail (a timeout, a refusal), the checks at ordinary contracts
 * stand, with that failure: a unit accepted there is accepted with no
 * stronger module fact. */
export function verifyByUnits(fragment: string, key: string, names: string, options: InterfaceOptions): CheckedUnits {
  mkdirSync(options.work, { recursive: true });
  const environment: Record<string, string> = {};
  if (process.env.TSCERT_PASS_REFUSALS === "raw") environment.TSCERT_PASS_REFUSALS = "raw";
  const check = (path: string): WorkerRun => invokeWorker(verifierCall(verifier,
    ["--subtype-rounds", String(options.rounds), "--file-worker", String(options.mode),
      fragment, path, key, String(options.fuel), names], environment), fileWorkerProtocol, options.invocation);
  const ordinary = join(options.work, "ordinary-interfaces.json");
  writeFileSync(ordinary, canonical({ modules: [] }));
  // A file that reads no module needs no interface; one that does is
  // checked at its modules' interfaces, and at ordinary contracts only
  // where they are not established.
  if (array(object(json(readFileSync(fragment, "utf8"))).modules).length === 0) return { run: check(ordinary), interfaceFailure: null };
  let interfaces: PreparedInterfaces;
  try {
    interfaces = prepareInterfaces(fragment, { ...options, names });
  } catch (error) {
    return { run: check(ordinary), interfaceFailure: error instanceof Error ? error.message : String(error) };
  }
  if (array(object(json(readFileSync(interfaces.path, "utf8"))).modules).length === 0)
    return { run: check(ordinary), interfaceFailure: null };
  return { run: check(interfaces.path), interfaceFailure: null };
}

/** The importer is one process stage, with every file it reads an explicit
 * input role. */
export function verifyWithInterfaces(fragment: string, key: string, names: string,
    options: InterfaceOptions): { run: Invoked; interfaces: PreparedInterfaces } {
  mkdirSync(options.work, { recursive: true });
  const environment: Record<string, string> = {};
  if (options.force.length > 0) environment.TSCERT_FORCE = options.force.join(",");
  // The pass's own refusal text, unlocated (`TSCERT_PASS_REFUSALS=raw`): part
  // of the stage's environment, so its key.
  if (process.env.TSCERT_PASS_REFUSALS === "raw") environment.TSCERT_PASS_REFUSALS = "raw";
  const check = (path: string): Invoked => invokeProcess(verifierCall(verifier,
    ["--subtype-rounds", String(options.rounds), "--verify-interface-stage", String(options.mode),
      fragment, path, key, String(options.fuel), names], environment),
    options.invocation);
  // A completed importer check at ordinary contracts needs no stronger
  // module facts. This publishes only that check, never a module interface.
  // Explicit own-module publication always runs the canonical computation.
  const ordinary = join(options.work, "ordinary-interfaces.json");
  writeFileSync(ordinary, canonical({ modules: [] }));
  const attempt = options.ownModule === undefined && options.force.length === 0 ? check(ordinary) : undefined;
  if (attempt?.status === 0)
    return { run: attempt, interfaces: { path: ordinary, records: [] } };
  if (attempt !== undefined && attempt.status !== 1)
    throw Error(`importer stage ${attempt.record.execution}: ${attempt.stderr}`);
  if (attempt !== undefined && array(object(json(readFileSync(fragment, "utf8"))).modules).length === 0)
    return { run: attempt, interfaces: { path: ordinary, records: [] } };
  const interfaces = prepareInterfaces(fragment, { ...options, names });
  if (attempt !== undefined && array(object(json(readFileSync(interfaces.path, "utf8"))).modules).length === 0)
    return { run: attempt, interfaces };
  let importerInterfaces = interfaces.path;
  if (options.ownModule !== undefined) {
    const locations = array(object(json(readFileSync(fragment, "utf8"))).modules).map((m) => string(object(m).location));
    const modules = array(object(json(readFileSync(interfaces.path, "utf8"))).modules)
      .filter((row) => locations.includes(string(object(object(row).module).location)));
    importerInterfaces = join(options.work, "importer-interfaces.json");
    writeFileSync(importerInterfaces, canonical({ modules }));
  }
  const run = check(importerInterfaces);
  return { run, interfaces };
}
