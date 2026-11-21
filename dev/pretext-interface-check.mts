import { copyFileSync, cpSync, lstatSync, mkdirSync, mkdtempSync, writeFileSync } from "node:fs";
import { basename, join } from "node:path";
import { verifyByUnits } from "../pipeline/module-interfaces.mts";
import { Recorder, readInvocationLog } from "../pipeline/stages.mts";
import { decodeVerdictLine, type VerdictLine } from "../pipeline/stage-execution.mts";
import { invocationLog, memberName, parseSource, readFragmentFile, stepTimeoutMs } from "../pipeline/verify-source.mts";
import type { JsonRead } from "../tools/calculus.mts";
import type { CallEffect, Exits, Frame, IndexFact, TypeTerm } from "../tools/declaration-types.mts";
import { withConditions } from "../tools/type-graph.mts";
import { checkedFrame, declarationDigests, declarationName, digest, list, object, read, string } from "./pretext-interface-bundle.mts";

const hasFrame = (frame: Frame): boolean => frame.some((r) => r.change !== "any");
const hasExitFrame = (frames: Exits<Frame>): boolean => hasFrame(frames.normal) || hasFrame(frames.exceptional);

function withExitFrames(effect: CallEffect, frames: Exits<Frame>): CallEffect {
  return { ...effect, exits: {
    normal: { ...effect.exits.normal, frame: frames.normal },
    exceptional: { ...effect.exits.exceptional, frame: frames.exceptional },
  } };
}

function readExitFrames(entry: JsonRead): Exits<Frame> {
  const { normal, exceptional } = object(entry);
  return { normal: checkedFrame(normal), exceptional: checkedFrame(exceptional) };
}
function verified(verdict: VerdictLine, verdicts: Map<string, VerdictLine>): boolean {
  const pending = [verdict];
  const seen = new Set<string>();
  for (const v of pending) {
    if (seen.has(v.unit)) continue;
    seen.add(v.unit);
    if (!("accepted" in v)) return false;
    for (const unit of v.depends) {
      const dependency = verdicts.get(unit);
      if (dependency === undefined) return false;
      pending.push(dependency);
    }
  }
  return true;
}

type OpenInterface = {
  declarations: string;
  frames: { readonly [name: string]: JsonRead };
  statedDigests: [string, string][];
  compilerOptions: { readonly [name: string]: JsonRead };
};

type CheckResult = {
  passed: Set<string>;
  used: string[];
  detail: string;
  refusals: Map<string, string>;
};

export function openInterface(bundle: string): OpenInterface {
  const declarations = join(bundle, "declarations");
  const supplied = object(read(join(bundle, "frames.json")));
  const frames = object(supplied.modules);
  const digests = object(supplied.declarations);
  const stated = object(supplied.stated);
  const bundleDigests = declarationDigests(declarations);
  if (Object.keys(digests).length !== Object.keys(bundleDigests).length ||
      Object.entries(bundleDigests).some(([name, hash]) => digests[name] !== hash))
    throw Error("declarations differ from the produced interface");
  const statedDigests = Object.entries(stated).map(([name, entry]): [string, string] => {
    const { declarationSha256, sourceSha256, units } = object(entry);
    const hash = string(declarationSha256);
    if (bundleDigests[name] !== hash || !/^[0-9a-f]{64}$/.test(string(sourceSha256)) ||
        list(units).length === 0 || !list(units).every((unit) => typeof unit === "string"))
      throw Error(`invalid publication of stated effects: ${name}`);
    return [name, hash];
  });
  return { declarations, frames, statedDigests, compilerOptions: object(supplied.compilerOptions) };
}

/** Check one source file using the declarations and contracts in the supplied bundle. */
export function checkWithInterface(source: string, bundle: OpenInterface, work: string): CheckResult {
  const { declarations, frames, statedDigests, compilerOptions } = bundle;
  const file = basename(source);
  const dir = mkdtempSync(join(work, `${file}-`));
  const src = join(dir, "src");
  const artifacts = join(dir, "artifacts");
  mkdirSync(artifacts, { recursive: true });
  const own = join(declarations, declarationName(file));
  cpSync(declarations, src, { recursive: true, filter: (path) => {
    const stat = lstatSync(path);
    return stat.isDirectory() || (stat.isFile() && path !== own && path.endsWith(".d.ts"));
  } });
  const implementation = join(src, file);
  copyFileSync(source, implementation);
  const project = join(dir, "tsconfig.json");
  writeFileSync(project, JSON.stringify({ compilerOptions, files: [implementation], include: ["src/**/*.d.ts"] }));
  const log = join(artifacts, invocationLog);
  const recorder = new Recorder(log);
  const publishedEffects = new Map(statedDigests.filter(([name]) => join(declarations, name) !== own)
    .map(([name, hash]): [string, string] => [join(src, name), hash]));
  const { parsed } = parseSource(implementation, project, artifacts, recorder, [], publishedEffects);
  const checkBoundary = (): void => {
    if (readInvocationLog(log).some((r) => r.stage === "module" || r.stage === "interface-plan" || r.stage === "module-interface"))
      throw Error(`${file}: consumer ran a dependency stage`);
  };
  checkBoundary();
  if (parsed.code !== 0) return { passed: new Set<string>(), used: [], detail: parsed.detail, refusals: new Map<string, string>() };
  const fragment = join(artifacts, "fragment.json");
  writeFileSync(fragment, parsed.out);
  const ast = readFragmentFile(fragment);
  if (ast.modules.length !== 0) throw Error(`${file}: consumer resolved a dependency implementation`);
  const used = new Set<string>();
  for (const value of ast.declarations.values) {
    const published = frames[value.declaration.module];
    if (published === undefined || value.construct) continue;
    const { declarationSha256, effects, conditions } = object(published);
    const named = (entries: JsonRead): JsonRead => {
      const table = object(entries);
      return Object.hasOwn(table, value.declaration.name) ? table[value.declaration.name] : undefined;
    };
    const frame = named(effects);
    const clauses = named(conditions);
    if (frame === undefined && clauses === undefined) continue;
    if (!value.declaration.module.startsWith("./src/") || !value.declaration.module.endsWith(".d.ts") ||
        declarationSha256 !== digest(join(dir, value.declaration.module)))
      throw Error(`${file}: contract does not match its resolved declaration file`);
    for (const entry of [frame, clauses]) {
      if (entry === undefined) continue;
      const span = list(object(entry).span);
      if (span.length !== 2 || span.some((offset, i) => offset !== value.declaration.span[i]))
        throw Error(`${file}: contract does not match its resolved declaration span`);
    }
    if (frame !== undefined) {
      if (value.type.k !== "function" || value.typeParams.length) throw Error(`${file}: expected one fixed signature`);
      const entry = object(frame);
      const call = readExitFrames(entry.call);
      const returned = readExitFrames(entry.returned);
      const apply = (type: Extract<TypeTerm, { k: "function" }>, frames: Exits<Frame>): void => {
        if (hasFrame(type.effect.exits.normal.frame) || hasFrame(type.effect.exits.exceptional.frame))
          throw Error(`${file}: the declaration already states a frame for ${value.declaration.name}`);
        type.effect = withExitFrames(type.effect, frames);
      };
      apply(value.type, call);
      if (hasExitFrame(returned)) {
        if (value.type.result.k !== "function") throw Error(`${file}: expected a fixed returned signature`);
        apply(value.type.result, returned);
      }
    }
    if (clauses !== undefined) {
      const entry = object(clauses);
      const facts = (wire: JsonRead): readonly IndexFact[] =>
        list(wire) as readonly IndexFact[]; // asserted: the producer writes its checked fragment's facts and Lean decodes them
      const requires = facts(entry.requires);
      const ensures = facts(entry.ensures);
      const attach = (term: TypeTerm): TypeTerm => {
        if (term.k !== "function") throw Error(`${file}: call conditions require a function signature`);
        return { ...term, effect: withConditions(term.effect, requires, ensures) };
      };
      value.type = value.type.k === "intersection" ? { ...value.type, parts: value.type.parts.map(attach) } : attach(value.type);
    }
    used.add(value.binding.local);
  }
  writeFileSync(fragment, JSON.stringify(ast));
  const { run } = verifyByUnits(fragment, ast.file, "", { mode: 8, fuel: 12, rounds: 4096, force: [],
    work: join(artifacts, "interfaces"), invocation: { limitMs: stepTimeoutMs, recorder, force: false } }, false);
  checkBoundary();
  if (run.preparation.status !== 0) throw Error(run.preparation.stderr);
  const verdicts = new Map<string, VerdictLine>();
  for (const part of run.parts) {
    if (!part.stdout.trim()) throw Error(`${file}: missing verdict for ${part.part}: ${part.stderr}`);
    const v = decodeVerdictLine(part.stdout.trim());
    verdicts.set(v.unit, v);
  }
  const passed = new Set([...verdicts.values()].filter((v) => verified(v, verdicts)).flatMap((v) => v.members.map(memberName)));
  const refusals = new Map<string, string>();
  for (const verdict of verdicts.values()) {
    if (verified(verdict, verdicts)) continue;
    for (const member of verdict.members.map(memberName))
      refusals.set(member, "refusal" in verdict ? verdict.refusal.split("\n")[0] : "a dependency or client assumption remains");
  }
  return { passed, used: [...used], detail: "", refusals };
}
