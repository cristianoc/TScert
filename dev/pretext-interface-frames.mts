// The two commands are independent. Only the producer has the dependency sources.
// node dev/pretext-interface-frames.mts produce <pretext> <bundle> <producer-work>
// node dev/pretext-interface-frames.mts measure <pretext> <bundle> <consumer-work>
// The measure command takes each consumer's own source from <pretext> and gives
// the verifier an isolated project with that source and the bundle alone.
import { spawnSync } from "node:child_process";
import { createHash } from "node:crypto";
import { copyFileSync, cpSync, lstatSync, mkdirSync, mkdtempSync, readFileSync, readdirSync, writeFileSync } from "node:fs";
import { join, resolve } from "node:path";
import { prepareInterfaces, verifyByUnits } from "../pipeline/module-interfaces.mts";
import { Recorder, readInvocationLog } from "../pipeline/stages.mts";
import { decodeVerdictLine, type VerdictLine } from "../pipeline/stage-execution.mts";
import { check, invocationLog, memberName, parseSource, readFragmentFile, stepTimeoutMs } from "../pipeline/verify-source.mts";
import { isJsonList, isJsonObject, type JsonRead } from "../tools/calculus.mts";
import { SymbolFlags } from "../tools/node_modules/typescript/dist/api/sync/api.js";
import { isFunctionDeclaration, isIdentifier, isTypeReferenceNode, type Node } from "../tools/node_modules/typescript/dist/ast/index.js";
import { inDeclarationAttempt, inDeclarationSession } from "../tools/declaration-session.mts";
import { close, initOmission, lowerModule } from "../tools/fragment-parse.mts";
import { withConditions } from "../tools/type-graph.mts";
import type { CallEffect, Change, DeclarationIdentity, Exits, Frame, IndexFact, TypeTerm } from "../tools/declaration-types.mts";

const repo = resolve(import.meta.dirname, "..");
const digest = (path: string): string => createHash("sha256").update(readFileSync(path)).digest("hex");
const read = (path: string): JsonRead => JSON.parse(readFileSync(path, "utf8"));
function list(value: JsonRead): readonly JsonRead[] {
  if (!isJsonList(value)) throw Error("expected an array");
  return value;
}
function object(value: JsonRead): { readonly [name: string]: JsonRead } {
  if (!isJsonObject(value)) throw Error("expected an object");
  return value;
}
function string(value: JsonRead): string {
  if (typeof value !== "string") throw Error("expected a string");
  return value;
}

function checkedFrame(value: JsonRead): Frame {
  const classes = ["value", "array", "view"];
  const entries = list(value);
  if (entries.length !== classes.length) throw Error("expected one frame entry per class");
  return entries.map((entry, i) => {
    const { region, change } = object(entry);
    const cls = object(object(region).cls);
    function grade(v: JsonRead): Change {
      switch (v) {
        case "keep": case "init": case "scalar": case "extend": case "grow": case "any": return v;
        default: throw Error("expected a change grade");
      }
    }
    if (classes.some((c) => cls[c] !== (c === classes[i]))) throw Error("unexpected frame class");
    return { region: { cls: { value: i === 0, array: i === 1, view: i === 2 } }, change: grade(change) };
  });
}

function command(binary: string, args: string[], cwd: string = repo): string {
  const result = spawnSync(binary, args, { cwd, encoding: "utf8" });
  if (result.status !== 0) throw Error(result.error?.message ?? (result.stderr || result.stdout));
  return result.stdout.trim();
}

type PublishedConditions = { span: DeclarationIdentity["span"]; requires: IndexFact[]; ensures: IndexFact[] };
type PublishedEffect = { span: DeclarationIdentity["span"]; call: Exits<Frame>; returned: Exits<Frame> };
type PublishedContracts = { declarationSha256: string; effects: Record<string, PublishedEffect>;
  conditions: Record<string, PublishedConditions> };

function exitFrames(entry: JsonRead): Exits<Frame> {
  const { normal, exceptional } = object(entry);
  return { normal: checkedFrame(object(normal).frame), exceptional: checkedFrame(object(exceptional).frame) };
}
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
const declarationName = (file: string): string => file.replace(/\.ts$/, ".d.ts");
const configuration = (extra: object): string => JSON.stringify({
  extends: join(pretext, "tsconfig.json"), compilerOptions: { types: [] }, ...extra,
});
const packageTypes = (): string => join(bundle, "declarations");

function declarationFiles(dir: string): string[] {
  return readdirSync(dir, { recursive: true, withFileTypes: true })
    .filter((entry) => entry.isFile() && entry.name.endsWith(".d.ts"))
    .map((entry) => join(entry.parentPath, entry.name)).sort();
}

function declarationDigests(dir: string): Record<string, string> {
  return Object.fromEntries(declarationFiles(dir).map((file) => [file.slice(dir.length + 1), digest(file)]));
}

function emittedDeclaration(path: string, config: string): {
  functions: Map<string, DeclarationIdentity["span"]>; statesEffects: boolean;
} {
  return inDeclarationAttempt(() => inDeclarationSession(path, config, (project) => {
    const source = project?.program.getSourceFile(path);
    if (project === undefined || source === undefined) throw Error(`TypeScript did not load ${path}`);
    const checker = project.checker;
    const module = checker.getSymbolAtLocation([source])[0];
    if (module === undefined) throw Error(`TypeScript did not resolve the module of ${path}`);
    const declarations = new Map<string, DeclarationIdentity["span"]>();
    for (const symbol of checker.getExportsOfModule(module)) {
      const target = symbol.flags & SymbolFlags.Alias ? checker.getAliasedSymbol(symbol) : symbol;
      const declaration = target?.declarations.length === 1 ? target.declarations[0]?.resolve() : undefined;
      if (declaration === undefined || declaration.getSourceFile().fileName !== path ||
          !isFunctionDeclaration(declaration) || declaration.name === undefined) continue;
      declarations.set(declaration.name.text, [declaration.getStart(source), declaration.end]);
    }
    const statesEffects = (node: Node): boolean =>
      (isTypeReferenceNode(node) && isIdentifier(node.typeName) && node.typeName.text === "Modifies") ||
      (node.forEachChild((child) => statesEffects(child) || undefined) ?? false);
    return { functions: declarations, statesEffects: statesEffects(source) };
  }));
}

function produce(files: string[]): void {
  if (command("git", ["-C", pretext, "status", "--porcelain", "--", "src", "tsconfig.json", "tsconfig.build.json", "package.json"]))
    throw Error("producer requires a clean source checkout");
  mkdirSync(bundle);
  command(join(repo, "tools/node_modules/.bin/tsc"), ["-p", join(pretext, "tsconfig.build.json"),
    "--emitDeclarationOnly", "--declarationMap", "false", "--outDir", packageTypes()]);
  copyFileSync(join(pretext, "src/resolvable.d.ts"), join(packageTypes(), "resolvable.d.ts"));
  const project = join(work, "producer-project.json");
  writeFileSync(project, configuration({
    include: [join(pretext, "src/**/*.ts")], exclude: [join(pretext, "src/layout.test.ts")],
  }));
  const emitted = join(work, "emitted-project.json");
  writeFileSync(emitted, configuration({ include: [join(packageTypes(), "**/*.d.ts")], exclude: [] }));
  const manifest: Record<string, PublishedContracts> = {};
  const stated: Record<string, { declarationSha256: string; sourceSha256: string; units: string[] }> = {};
  for (const file of files) {
    console.log(`produce ${file}`);
    const dir = join(work, file);
    mkdirSync(dir, { recursive: true });
    const absolute = join(pretext, "src", file);
    const location = `./src/${file}`;
    const recorder = new Recorder(join(dir, invocationLog));
    const { parsed } = parseSource(absolute, project, dir, recorder);
    if (parsed.code !== 0) throw Error(parsed.detail);
    const own = inDeclarationAttempt(() => lowerModule({ absolute, location, tsconfigPath: project, selection: undefined }));
    if (own.refused !== undefined) throw Error(own.refused);
    const ownModule = join(dir, "own-module.json");
    writeFileSync(ownModule, JSON.stringify(own.module));
    const stable = new Set<string>(list(JSON.parse(command("lake", ["env", "lean", "--run",
      join(repo, "dev/pretext-interface-stability.lean"), ownModule], join(repo, "lean")))).map(string));
    const fragment = join(dir, "fragment.json");
    writeFileSync(fragment, parsed.out);
    const result = prepareInterfaces(fragment, { mode: 8, fuel: 12, rounds: 4096, force: [], work: dir,
      invocation: { limitMs: stepTimeoutMs, force: false, recorder }, ownModule });
    const published = list(object(read(result.path)).modules).map(object)
      .find((r) => object(r.module).location === location);
    if (published === undefined) throw Error(`missing producer result for ${file}`);
    const declaration = declarationName(file);
    const declarationFile = join(packageTypes(), declaration);
    const declarationSha256 = digest(declarationFile);
    const { functions: exports, statesEffects } = emittedDeclaration(declarationFile, emitted);
    const hasConditions = own.module.functions.some((fn) =>
      exports.has(fn.name) && (fn.requires.length > 0 || fn.ensures.length > 0));
    const conditions: Record<string, PublishedConditions> = {};
    if (statesEffects || hasConditions) {
      console.log("  checking the module's stated contracts");
      using checked = check(absolute, project, false, undefined, true);
      if (checked.status !== "verified") throw Error(`${file}: stated contracts were not verified: ${checked.detail}`);
      const checkedFragment = readFragmentFile(join(checked.artifacts, "fragment.json"));
      if (checkedFragment.sourceSha256 !== own.module.sourceSha256)
        throw Error(`${file}: stated contracts were checked against different source bytes`);
      if (checked.units === undefined || checked.units.length === 0 || checked.units.some((unit) => unit.status !== "verified"))
        throw Error(`${file}: stated contracts require complete unit verdicts`);
      if (checked.initialization.length && !checked.units.some((unit) => unit.unit === "init"))
        throw Error(`${file}: stated contracts require an initialization verdict`);
      const units = checked.units.map((unit) => unit.unit);
      const checkedMembers = new Set(checked.units.flatMap((unit) => unit.members));
      for (const fn of checkedFragment.functions) {
        const span = exports.get(fn.name);
        if (span === undefined || (fn.requires.length === 0 && fn.ensures.length === 0)) continue;
        if (!stable.has(fn.name) || !checkedMembers.has(`${fn.name}@${fn.namePos[0]}`) || Object.hasOwn(conditions, fn.name))
          throw Error(`${file}: no single checked binding for ${fn.name}'s stated conditions`);
        conditions[fn.name] = { span, requires: fn.requires, ensures: fn.ensures };
      }
      copyFileSync(join(checked.artifacts, invocationLog), join(dir, "stated-invocations.jsonl"));
      if (statesEffects) stated[declaration] = { declarationSha256, sourceSha256: checkedFragment.sourceSha256, units };
      console.log(`  checked ${units.length} units, published conditions for ${Object.keys(conditions).length} exports`);
    }
    const effects: PublishedContracts["effects"] = Object.fromEntries(list(published.entries).map(object).flatMap((entry) => {
      const name = string(entry.name);
      const span = exports.get(name);
      if (span === undefined || entry.established === null || !stable.has(name)) return [];
      const fns = own.module.functions.filter((f) => f.name === name);
      const [fn] = fns;
      // A projection of one fixed ordinary signature and its returned callable.
      // Their frames come from the checked row at the declared signature.
      if (fn === undefined || fns.length !== 1 ||
          ((fn.requires.length || fn.ensures.length) && !Object.hasOwn(conditions, name)) ||
          fn.guard !== null || fn.stated !== null || fn.typeParams.length || fn.params.some((p) => p.rest) ||
          fn.completion !== "sync") return [];
      const checked = object(entry.established);
      const call = exitFrames(checked.exits);
      const returned = exitFrames(checked.resultExits);
      return hasExitFrame(call) || hasExitFrame(returned) ? [[name, { span, call, returned }]] : [];
    }));
    manifest[`./src/${declaration}`] = { declarationSha256, effects, conditions };
    console.log(`  published effects for ${Object.keys(effects).length} exports`);
  }
  writeFileSync(join(bundle, "frames.json"), JSON.stringify({ declarations: declarationDigests(packageTypes()),
    modules: manifest, stated }, null, 2) + "\n");
  close();
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

function measure(expected: { readonly [file: string]: JsonRead }): void {
  const supplied = object(read(join(bundle, "frames.json")));
  const frames = object(supplied.modules);
  const digests = object(supplied.declarations);
  const stated = object(supplied.stated);
  const bundleDigests = declarationDigests(packageTypes());
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
  let total = 0;
  let accepted = 0;
  for (const [file, record] of Object.entries(expected)) {
    const baseline = Object.entries(object(record)).filter(([name, result]) => name !== initOmission && result === "verified");
    total += baseline.length;
    const dir = mkdtempSync(join(work, `${file}-`));
    const src = join(dir, "src");
    const artifacts = join(dir, "artifacts");
    mkdirSync(artifacts, { recursive: true });
    const own = join(packageTypes(), declarationName(file));
    cpSync(packageTypes(), src, { recursive: true, filter: (path) => {
      const stat = lstatSync(path);
      return stat.isDirectory() || (stat.isFile() && path !== own && path.endsWith(".d.ts"));
    } });
    const implementation = join(src, file);
    copyFileSync(join(pretext, "src", file), implementation);
    copyFileSync(join(pretext, "package.json"), join(dir, "package.json"));
    const project = join(dir, "tsconfig.json");
    writeFileSync(project, configuration({ files: [implementation], include: ["src/**/*.d.ts"], exclude: [] }));
    const log = join(artifacts, invocationLog);
    const recorder = new Recorder(log);
    const publishedEffects = new Map(statedDigests.filter(([name]) => join(packageTypes(), name) !== own)
      .map(([name, hash]): [string, string] => [join(src, name), hash]));
    const { parsed } = parseSource(implementation, project, artifacts, recorder, [], publishedEffects);
    const checkBoundary = (): void => {
      if (readInvocationLog(log).some((r) => r.stage === "module" || r.stage === "interface-plan" || r.stage === "module-interface"))
        throw Error(`${file}: consumer ran a dependency stage`);
    };
    checkBoundary();
    if (parsed.code !== 0) {
      console.log(`${file}: 0/${baseline.length}, ${parsed.detail.split("\n")[0]}`);
      continue;
    }
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
    const lost = baseline.filter(([name]) => !passed.has(name)).map(([name]) => name);
    const count = baseline.length - lost.length;
    accepted += count;
    console.log(`${file}: ${count}/${baseline.length}, contracts [${[...used].join(", ")}]`);
    for (const name of lost) {
      const verdict = [...verdicts.values()].find((v) => v.members.some((m) => memberName(m) === name));
      const cause = verdict === undefined ? "no verdict" : "refusal" in verdict ? verdict.refusal.split("\n")[0]
        : "a dependency or client assumption remains";
      console.log(`  missing ${name}: ${cause}`);
    }
  }
  console.log(`Pretext: ${accepted}/${total} previously verified functions retained`);
  close();
}

const [mode, source, output, scratch] = process.argv.slice(2);
if (!source || !output || !scratch || (mode !== "produce" && mode !== "measure"))
  throw Error("expected produce|measure <pretext> <bundle> <work>");
const pretext = resolve(source);
const bundle = resolve(output);
const work = resolve(scratch);
mkdirSync(work, { recursive: true });
const head = command("git", ["-C", pretext, "rev-parse", "HEAD"]);
const expected = object(object(read(join(repo, "tests/pretext-tier-expected.json")))[head]);
if (mode === "produce") produce(Object.keys(expected));
else measure(expected);
