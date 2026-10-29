// Observable behaviour of the real makers and handlers; no miniature table.
import assert from "node:assert/strict";
import { refusal, refusalOf } from "../tools/diagnostic-gate.mts";
import { ioFailure, ioFailureOf, toolFailureOf } from "../tools/thrown.mts";
import { orAbsent } from "../tools/files.mts";

const gateError = refusal("blocked", [3, 8]);
assert.deepEqual(refusalOf(gateError), { pos: [3, 8], message: "blocked" });
assert.strictEqual(refusalOf(gateError), refusalOf(gateError));
assert.equal(gateError.message, "blocked");
assert.equal("pos" in gateError, false);
for (const foreign of [null, undefined, 1, "blocked", {}, new Error("blocked"), () => {}]) {
  assert.equal(refusalOf(foreign), undefined);
  assert.equal(ioFailureOf(foreign), undefined);
}
const trapped = new Proxy({}, { get() { throw Error("lookup reads no field"); } });
assert.equal(refusalOf(trapped), undefined);
assert.equal(ioFailureOf(trapped), undefined);

const cause = { code: "ENOENT" };
const missing = ioFailure("read", "missing", cause);
const operation = (): never => { throw missing; };
assert.equal(orAbsent(operation, "missing"), null);
assert.equal(orAbsent(operation, "missing"), null);
assert.equal(ioFailureOf(missing)?.cause, cause);
const report = toolFailureOf(missing);
assert.equal(report?.kind, "io");
assert.match(report?.caller ?? "", /^caught-errors\.mts:\d+$/);
assert.equal(toolFailureOf(new Error("wrapper", { cause: missing }))?.caller, report?.caller);
const denied = ioFailure("read", "denied", { code: "EACCES" });
for (let i = 0; i < 2; i++) {
  assert.throws(() => orAbsent(() => { throw denied; }, "denied"), (error: unknown) => error === denied);
}
console.log("caught errors: repeated lookup and handling, foreign values, caller attribution");
