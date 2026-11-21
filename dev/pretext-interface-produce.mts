import { spawnSync } from "node:child_process";
import { copyFileSync, mkdirSync, writeFileSync } from "node:fs";
import { join, resolve } from "node:path";
import { prepareInterfaces } from "../pipeline/module-interfaces.mts";
import { Recorder } from "../pipeline/stages.mts";
import { check, invocationLog, parseSource, readFragmentFile, stepTimeoutMs } from "../pipeline/verify-source.mts";
import type { JsonRead } from "../tools/calculus.mts";
import { SymbolFlags } from "../tools/node_modules/typescript/dist/api/sync/api.js";
import { isFunctionDeclaration, isIdentifier, isTypeReferenceNode, type Node } from "../tools/node_modules/typescript/dist/ast/index.js";
import { inDeclarationAttempt, inDeclarationSession } from "../tools/declaration-session.mts";
import { close, lowerModule } from "../tools/fragment-parse.mts";
import type { DeclarationIdentity, Exits, Frame, IndexFact } from "../tools/declaration-types.mts";
import { checkedFrame, declarationDigests, declarationName, digest, list, object, read, string } from "./pretext-interface-bundle.mts";

const repo = resolve(import.meta.dirname, "..");
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

export function produce(pretext: string, bundle: string, work: string, files: string[]): void {
  const configuration = (extra: object): string => JSON.stringify({
    extends: join(pretext, "tsconfig.json"), compilerOptions: { types: [] }, ...extra,
  });
  const packageTypes = (): string => join(bundle, "declarations");
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
  const config = object(JSON.parse(command(join(repo, "tools/node_modules/.bin/tsc"),
    ["--showConfig", "-p", join(pretext, "tsconfig.json")])));
  const compilerOptions = { ...object(config.compilerOptions), types: [] };
  writeFileSync(join(bundle, "frames.json"), JSON.stringify({ declarations: declarationDigests(packageTypes()),
    modules: manifest, stated, compilerOptions }, null, 2) + "\n");
  close();
}
