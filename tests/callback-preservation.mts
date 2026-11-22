import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import { pathToFileURL } from "node:url";
import { readFileSync, readdirSync, writeFileSync } from "node:fs";
import { join, resolve } from "node:path";
import { check } from "../pipeline/verify-source.mts";
import { runDirectory } from "../pipeline/run-directory.mts";

const dir = runDirectory("callback-preservation-");
const paper = readFileSync(new URL(
  "../docs/drafts/inferred-callback-preservation-note/note.tex", import.meta.url), "utf8");
const checksDir = new URL("../lean/Verification/Source/Claims/", import.meta.url);
const checkSources = readdirSync(checksDir).filter(name => name.startsWith("Callback") && name.endsWith(".lean"))
  .map(name => readFileSync(new URL(name, checksDir), "utf8"));
checkSources.push(readFileSync(new URL("../lean/Verification/Source/RequestCli.lean", import.meta.url), "utf8"));
const executableScope = new Set(checkSources.flatMap(source =>
  Array.from(source.matchAll(/scopeRefusal "([A-Za-z]+)"/g), match => match[1])));
const documentedScope = new Set(Array.from(paper.matchAll(/\\scopecheck\{([A-Za-z]+)\}/g), match => match[1]));
assert.deepEqual(documentedScope, executableScope, "paper scope and worker refusal names differ");

function paperExample(section: string): string {
  const sectionStart = paper.indexOf(`\\section{${section}}`);
  assert.ok(sectionStart >= 0, section);
  const listing = /\\begin\{lstlisting\}\[language=TypeScript\]\n([\s\S]*?)\\end\{lstlisting\}/
    .exec(paper.slice(sectionStart));
  assert.ok(listing, section);
  return listing[1];
}
const walker = paperExample("The problem");
const clients = paperExample("Examples and evidence");
const directCallers = `
export function preserves(xs: number[]): number {
  return walk(xs, () => {});
}
export function shrinks(xs: number[]): number {
  return walk(xs, () => { xs.pop(); });
}
export function head(xs: number[], visit: InferPreserves<() => void>): number {
  if (xs.length === 0) return 0;
  visit();
  return xs[0]!;
}
export function preservesHead(xs: number[]): number {
  return head(xs, () => {});
}
export function dropsHead(xs: number[]): number {
  return head(xs, () => { xs.pop(); });
}
`;
const forwarder = `
export function through(xs: number[], visit: InferPreserves<Visitor>): number {
  return walk(xs, visit);
}
`;
const forwardedClient = `
export function throughAlias(xs: number[]): number {
  return through(xs, i => { xs.push(i); });
}
`;
const argumentWalker = walker
  .replace("type Visitor = (i: number) => void;", "type ArgumentVisitor = (target: number[], i: number) => void;")
  .replace("function walk(xs: number[], visit: InferPreserves<Visitor>)", "function walkWithTarget(xs: number[], target: number[], visit: InferPreserves<ArgumentVisitor>)")
  .replace("visit(c.i)", "visit(target, c.i)");
const argumentClients = `
export function appendToTarget(xs: number[]): number {
  const target: number[] = [];
  return walkWithTarget(xs, target, (destination, i) => { destination.push(i); });
}
export function appendToAliasedTarget(xs: number[]): number {
  return walkWithTarget(xs, xs, (destination, i) => { destination.push(i); });
}
`;
const phaseProducer = `
type PhaseBox = { data: number[] };
export function headAfter(xs: number[], box: PhaseBox, visit: InferPreserves<() => void>): number {
  box.data = [];
  if (xs.length === 0) return 0;
  visit();
  return xs[0]!;
}
`;
const phaseClients = `
export function observeReplacement(box: {data: number[]}): number {
  return headAfter(box.data, box, () => {});
}
export function popOriginal(box: {data: number[]}): number {
  const old = box.data;
  return headAfter(old, box, () => { old.pop(); });
}
export function forwardFieldRead(box: {data: number[]}, visit: InferPreserves<() => void>): number {
  return headAfter(box.data, box, visit);
}
`;
const spreadProducer = `
type SpreadVisitor = (...args: (number[] | undefined)[]) => void;
export function walkSpread(xs: number[], target: number[], visit: InferPreserves<SpreadVisitor>): number {
  const parts: number[][] = [xs, xs];
  if (xs.length === 0) return 0;
  visit(...parts, target);
  return xs[0]!;
}
`;
const spreadClients = `
export function ignoreSpread(xs: number[]): number {
  return walkSpread(xs, [], () => {});
}
export function popSpread(xs: number[]): number {
  const target: number[] = [];
  return walkSpread(xs, target, (_?: number[], second?: number[], ...rest: (number[] | undefined)[]) => {
    if (second !== undefined) second.pop();
  });
}
export function spreadCallback(xs: number[]): number {
  const args: [number[], (i: number) => void] = [xs, () => { xs.pop(); }];
  return walk(...args);
}
`;
const shrinkingWrapper = `
export function shrink(xs: number[]): number {
  return walk(xs, () => { xs.pop(); });
}
export function head(xs: number[], visit: InferPreserves<() => void>): number {
  if (xs.length === 0) return 0;
  visit();
  return xs[0]!;
}
export function preservesHead(xs: number[]): number {
  return head(xs, () => {});
}
export function dropsHead(xs: number[]): number {
  return head(xs, () => { xs.pop(); });
}
`;
const capturedRoot = `
const shared: number[] = [1];
export function readShared(visit: InferPreserves<() => void>): number {
  if (shared.length === 0) return 0;
  visit();
  return shared[0]!;
}
export function callWithExtraArgument(): number {
  const unrelated: number[] = [2];
  const widened: (visit: () => void, unused: number[], extra: number[]) => number = readShared;
  return widened(() => { shared.pop(); }, unrelated, unrelated);
}
`;
const scopeExamples = `
export function postprocess(xs: number[]): number {
  return walk(xs, () => {}) + 1;
}
/** @ensures safeInteger(result) && 0 <= result */
export function statedExit(xs: number[]): number {
  return walk(xs, () => {});
}
function localVisitor(_i: number): void {}
export function useLocalVisitor(xs: number[]): number {
  return walk(xs, localVisitor);
}
export function useRestVisitor(xs: number[]): number {
  return walk(xs, (..._args: number[]) => {});
}
export function positiveHead(xs: number[], visit: InferPreserves<() => void>): boolean {
  if (xs.length === 0) return false;
  visit();
  return xs[0]! > 0;
}
export function guardedCaller(xs: number[]): xs is [number, ...number[]] {
  return positiveHead(xs, () => {});
}
export function guardedProducer(value: unknown, visit: InferPreserves<() => void>): value is number {
  visit();
  return typeof value === "number";
}
export function callGuardedProducer(value: unknown): boolean {
  return guardedProducer(value, () => {});
}
export function optionalArgument(xs: number[], visit: InferPreserves<() => void>, _mode?: number): number {
  if (xs.length === 0) return 0;
  visit();
  return xs[0]!;
}
export function omitArgument(xs: number[]): number {
  return optionalArgument(xs, () => {});
}
export function optionalCallback(xs: number[], visit: InferPreserves<(() => void) | undefined>): number {
  if (xs.length === 0) return 0;
  if (visit !== undefined) visit();
  return xs[0]!;
}
export function omitCallback(xs: number[]): number {
  return optionalCallback(xs, undefined);
}
/** @requires 0 < xs.length */
export function nonemptyHead(xs: number[], visit: InferPreserves<() => void>): number {
  visit();
  return xs[0]!;
}
export function callNonemptyHead(xs: number[]): number {
  return nonemptyHead(xs, () => {});
}
export function recursiveWalker(xs: number[], visit: InferPreserves<Visitor>): number {
  if (xs.length === 0) return 0;
  return recursiveWalker(xs, visit);
}
export async function asyncWalker(xs: number[], visit: InferPreserves<Visitor>): Promise<number> {
  visit(0);
  return xs.length;
}
`;
const annotations = resolve(import.meta.dirname, "../tools/resolvable.d.ts");
const project = join(dir, "tsconfig.json");
const combined = join(dir, "combined.ts");
const producer = join(dir, "producer.ts");
const consumer = join(dir, "consumer.ts");
writeFileSync(project, JSON.stringify({
  compilerOptions: { strict: true, target: "ES2022", module: "NodeNext" },
  files: [annotations, combined, producer, consumer],
}));
writeFileSync(combined, walker + directCallers + clients + forwarder + forwardedClient + argumentWalker + argumentClients +
  phaseProducer + phaseClients + spreadProducer + spreadClients + capturedRoot + scopeExamples);
writeFileSync(producer, walker + forwarder + argumentWalker + phaseProducer + spreadProducer + shrinkingWrapper);
writeFileSync(consumer, 'import { walk, through, walkWithTarget, headAfter, walkSpread, shrink } from "./producer.js";\n' + clients + forwardedClient + argumentClients + phaseClients + spreadClients + `
export function callShrinkingWrapper(xs: number[]): number {
  return shrink(xs);
}
`);

// The callback invalidates the indexed read, so the declared number result
// becomes undefined on a one-element array.
execFileSync(process.execPath, ["--input-type=module", "-e",
  `import { preservesHead, dropsHead } from ${JSON.stringify(pathToFileURL(combined).href)};
   if (preservesHead([7]) !== 7 || dropsHead([7]) !== undefined) process.exit(1);`]);

const exercisedScope = new Set<string>();
for (const source of [combined, consumer]) {
  const outcome = check(source, project, false, undefined, false,
    { omitted: [], select: null });
  assert.equal(outcome.status, "unverified", "detail" in outcome ? outcome.detail : source);
  assert.ok("units" in outcome && outcome.units, source);
  const detail = (name: string): string => {
    const member = outcome.units?.find(u => u.unit.startsWith(`${name}@`));
    assert.ok(member, name);
    return member.detail;
  };
  const refusesScope = (name: string, restriction: string): void => {
    const member = outcome.units?.find(u => u.unit.startsWith(`${name}@`));
    assert.equal(member?.status, "unverified", member?.detail ?? name);
    assert.ok(detail(name).includes(`callback scope [${restriction}]`), detail(name));
    exercisedScope.add(restriction);
  };
  if (source === combined) {
    const proved = outcome.units.find(u => u.unit.startsWith("preserves@"));
    assert.equal(proved?.status, "verified");
    assert.deepEqual(proved?.depends, []);
    assert.equal(outcome.units.find(u => u.unit.startsWith("preservesHead@"))?.status, "verified");
    assert.match(detail("dropsHead"), /fails its inferred preservation requirement/);
    assert.match(detail("shrinks"), /fails its inferred preservation requirement/);
    const collector = outcome.units.find(u => u.unit.startsWith("sumAndTrace@"));
    assert.equal(collector?.status, "verified", collector?.detail);
    assert.deepEqual(collector.depends, []);
    const producer = outcome.units.find(u => u.unit.startsWith("walk@"));
    assert.equal(producer?.status, "verified", producer?.detail);
    assert.match(producer.detail, /verified under inferred callback interface/);
    assert.match(detail("through"), /inferred callback interface checked experimentally/);
    assert.match(detail("walkSpread"), /"actualRoots":\[null\]/);
    assert.match(detail("spreadCallback"), /a spread obscures callback argument 2 at call of walk/);
    assert.match(detail("callWithExtraArgument"), /callback requirement for readShared refers outside its fixed parameters/);
    refusesScope("callWithExtraArgument", "referencesFixedParameters");
    refusesScope("through", "callbackProducerScope");
    refusesScope("spreadCallback", "fixedDirectApplication");
    refusesScope("ignoreSpread", "fixedCallbackSignature");
    refusesScope("observeReplacement", "readPrefixPlan");
    refusesScope("postprocess", "directCallbackReturn");
    refusesScope("statedExit", "callerPlainExit");
    refusesScope("useLocalVisitor", "readSourceModule");
    refusesScope("useRestVisitor", "readFixedLiteral");
    refusesScope("guardedCaller", "plainCallerResult");
    refusesScope("callGuardedProducer", "plainProducerResult");
    refusesScope("omitArgument", "readFixedArguments");
    refusesScope("omitCallback", "presentCallback");
    refusesScope("callNonemptyHead", "emptyProducerEntryFacts");
    refusesScope("recursiveWalker", "nonrecursiveDeclaration");
    refusesScope("asyncWalker", "ordinaryProducerGraph");
    assert.equal(outcome.units.find(u => u.unit.startsWith("appendToTarget@"))?.status, "verified");
  } else {
    assert.match(detail("sumAndTrace"), /inferred callback preservation checked experimentally/);
    refusesScope("sumAndTrace", "callbackCallerScope");
    assert.match(detail("spreadCallback"), /callback argument 2 at call of walk .* fails its inferred preservation requirement/);
    assert.match(detail("callShrinkingWrapper"), /shrink has no checked inferred callback interface/);
    assert.match(detail("ignoreSpread"), /inferred callback preservation checked experimentally/);
    assert.match(detail("observeReplacement"), /inferred callback preservation checked experimentally/);
    assert.match(detail("appendToTarget"), /inferred callback preservation checked experimentally/);
  }
  assert.match(detail("popSpread"), /fails its inferred preservation requirement/);
  assert.match(detail("popOriginal"), /fails its inferred preservation requirement/);
  assert.match(detail("forwardFieldRead"), /the forwarded requirement .* cannot name a caller input/);
  assert.match(detail("throughAlias"), /callback argument 2 at call of through .* fails its inferred preservation requirement/);
  assert.match(detail("appendToAliasedTarget"), /callback argument 3 at call of walkWithTarget .* fails its inferred preservation requirement/);
  assert.match(detail("sumAndAlias"), /callback argument 2 at call of walk .* fails its inferred preservation requirement/);
}
assert.deepEqual(exercisedScope, documentedScope, "each documented scope check needs a source refusal");

for (const [root, status] of [
  ["walk", "verified"], ["sumAndTrace", "verified"], ["sumAndAlias", "unverified"],
  ["preserves", "verified"], ["shrinks", "unverified"],
] as const) {
  const selected = check(combined, project, false, undefined, false,
    { omitted: [], select: [root] });
  assert.equal(selected.status, status, "detail" in selected ? selected.detail : root);
  assert.ok("units" in selected && selected.units);
  assert.deepEqual(selected.units.map(u => u.unit.split("@")[0]), [root]);
}
console.log("Verified the paper's producer and collector, and checked callback refusals for local and imported declarations.");
