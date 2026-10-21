// The pipeline cases (`make suite`): each case of the inventory whose file
// name contains a pattern, every case with none, several at once, each
// against its expected outcome, phase and diagnostic.
//   node pipeline/run-cases.mts module- generic-rest
// The controls no case can make are `test.mts`'s (`make test`).
import assert from "node:assert/strict";
import { availableParallelism } from "node:os";
import { join, resolve } from "node:path";
import { checkApart, type Outcome } from "./verify-source.mts";
import { linkFixtures } from "./fixture-links.mts";
// cases.mts is the inventory this runner judges: each case's source, project and expected status, phase and diagnostic.
import { cases, type Case } from "./cases.mts";

const here = import.meta.dirname;

/** Run one case's pipeline in its own process, as `verify-source.mts` does from the
 * command line, so that several cases run at once. */
export function runCase(test: Case): Promise<Outcome> {
  return checkApart(join(here, "examples", `${test.file}.ts`),
    test.project ? resolve(here, "..", test.project) : undefined, test.typescriptErrors)
    .catch((error: unknown) => { throw new Error(`${test.file}: ${error instanceof Error ? error.message : String(error)}`); });
}

/** Map over `items` with at most `width` in flight, keeping their order. The
 * count finished so far is shown on standard error: on one rewritten line in a
 * terminal, otherwise every tenth of the way. */
export async function pooled<T, R>(items: readonly T[], work: (item: T) => Promise<R>,
    width: number = availableParallelism()): Promise<PromiseSettledResult<R>[]> {
  const results: PromiseSettledResult<R>[] = new Array<PromiseSettledResult<R>>(items.length);
  let next = 0, finished = 0;
  const step = Math.max(1, Math.ceil(items.length / 10));
  const shown = () => {
    finished++;
    if (process.stderr.isTTY)
      process.stderr.write(`\r${finished} of ${items.length} cases${finished === items.length ? "\n" : ""}`);
    else if (finished % step === 0 || finished === items.length)
      process.stderr.write(`${finished} of ${items.length} cases\n`);
  };
  const worker = async () => {
    while (next < items.length) {
      const i = next++;
      try {
        results[i] = { status: "fulfilled", value: await work(items[i]) };
      } catch (reason) {
        results[i] = { status: "rejected", reason };
      }
      shown();
    }
  };
  await Promise.all<Promise<void>[]>(Array.from({ length: Math.min(width, items.length) }, worker));
  return results;
}

/** Require a case's expected outcome. */
export function expectOutcome(test: Case, result: Outcome): Outcome {
  assert.equal(result.status, test.status, `${test.file}: ${JSON.stringify(result)}`);
  assert.equal(result.phase, test.phase, `${test.file}: wrong boundary`);
  if (test.diagnostic) {
    assert.notEqual(result.status, "verified");
    if (result.status !== "verified")
      assert.match(result.detail, test.diagnostic, `${test.file}: wrong failure`);
  }
  if (result.status !== "verified" && test.kind === "negative" && (test.phase === "search" || test.phase === "check"))
    assert.match(result.detail, /at \[\d+,\d+\)|obligation at \d+/, `${test.file}: a control failing at no located obligation`);
  return result;
}

if (import.meta.filename === resolve(process.argv[1] ?? "")) {
  linkFixtures();
  const patterns = process.argv.slice(2);
  const selected = cases.filter((c) => !patterns.length || patterns.some((p) => c.file.includes(p)));
  if (!selected.length) {
    process.stderr.write(`no case matches ${patterns.join(" ")}\n`);
    process.exit(2);
  }
  let failed = 0, verifiedFunctions = 0;
  const outcomes = await pooled(selected, runCase);
  for (const [i, test] of selected.entries()) {
    try {
      const settled = outcomes[i];
      if (settled.status === "rejected") throw settled.reason;
      const result = expectOutcome(test, settled.value);
      if (result.status === "verified") verifiedFunctions += result.functions.length;
      process.stdout.write(`${test.file}: ${result.status} (${result.phase}, ${test.kind})\n`);
    } catch (error) {
      failed++;
      process.stdout.write(`${test.file}: FAILED ${error instanceof Error ? error.message.split("\n")[0] : error}\n`);
    }
  }
  process.stdout.write(`${selected.length - failed} of ${selected.length} cases as expected; ${verifiedFunctions} functions ` +
    `verified; ${selected.filter((c) => c.kind === "negative").length} negative controls; ` +
    `${selected.filter((c) => c.kind === "gap").length} named gaps\n`);
  process.exitCode = failed ? 1 : 0;
}
