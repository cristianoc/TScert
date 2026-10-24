// The controls of shared work (STAGE-STORE.md, "Shared work"), each over
// files and a compiler of its own, without a stage:
// - within an attempt a front-end operation at a path answers its first
//   answer, noted in a record begun after it; the next attempt, a ledger's
//   validation and a read standing for Node's read afresh; without sharing
//   a changed answer makes the attempt incomplete;
// - a query asked again of a snapshot is served its first answer, a query
//   of another snapshot is asked, and without sharing every query is asked;
// - every compiler's ledger is noted in a record before its first request,
//   asked or served, with the ledger's incompleteness.
import assert from "node:assert/strict";
import { mkdirSync, symlinkSync, unlinkSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import { runDirectory } from "../pipeline/run-directory.mts";
import { compilerLedger, openFrontEndCompiler, queryTelemetry, releaseCompiler } from "../tools/compiler-channel.mts";
import { newLedger, nodeResolve, observed, present, realPath, sharingForTests, unobservable, validateLedger, withLedger }
  from "../tools/files.mts";
import { syntax as ts } from "../tools/syntax.mts";


const dir = runDirectory("tscert-shared-work-");
const real = (path: string): string => realPath(path);

// --- attempt answers
{
  mkdirSync(join(dir, "a"));
  mkdirSync(join(dir, "b"));
  const link = join(dir, "l");
  symlinkSync(join(dir, "a"), link);
  const a = real(join(dir, "a")), b = real(join(dir, "b"));
  const relink = (to: string): void => {
    unlinkSync(link);
    symlinkSync(to, link);
  };
  const ledger = newLedger();
  const outer = observed(() => {
    assert.equal(withLedger(ledger, () => real(link)), a);
    relink(join(dir, "b"));
    const inner = observed(() => real(link));
    assert.equal(inner.value, a, "a later read of the attempt answers its first answer");
    assert.ok(inner.observations.some(([o, p, x]) => o === "real" && p === link && x === a),
      "and notes it in a record begun after it");
    assert.match(validateLedger(ledger) ?? "", /answers otherwise now/, "a ledger's validation reads afresh");
  });
  assert.equal(outer.incomplete, null);
  assert.equal(observed(() => real(link)).value, b, "the next attempt reads afresh");
  relink(join(dir, "a"));
  const unshared = sharingForTests(false, () => observed(() => {
    real(link);
    relink(join(dir, "b"));
    return real(link);
  }));
  assert.equal(unshared.value, b);
  assert.match(unshared.incomplete ?? "", /answered differently within the stage/, "without sharing a change is seen");
  // A read standing for Node's is made afresh: Node's resolution of a file
  // the front end found absent earlier in the attempt sees it.
  const target = join(dir, "late.mjs");
  const node = observed(() => {
    assert.equal(present(target), false);
    writeFileSync(target, "export {};\n");
    return nodeResolve("./late.mjs", join(dir, "main.mjs"));
  });
  assert.ok(node.value?.endsWith("/late.mjs"), `Node resolves the file it reads afresh: ${node.value}`);
  assert.match(node.incomplete ?? "", /answered differently within the stage/);
  process.stdout.write("attempt answers: first answers within an attempt, fresh across attempts, validations and Node's reads\n");
}

// --- query answers and compiler ledgers
{
  const project = join(dir, "project");
  mkdirSync(project);
  writeFileSync(join(project, "tsconfig.json"), JSON.stringify({ compilerOptions: { strict: true, noEmit: true }, include: ["*.ts"] }));
  const file = join(project, "a.ts");
  writeFileSync(file, "export const x: number = 1;\nexport function f(): number {\n  return x;\n}\n");
  const api = openFrontEndCompiler(project, new Map());
  try {
    const open = () => {
      const snapshot = api.updateSnapshot({ openFiles: [file] });
      const p = snapshot.getDefaultProjectForFile(file);
      assert.ok(p);
      const source = p.program.getSourceFile(file);
      assert.ok(source);
      const find = (node: ts.Node): ts.Identifier | undefined =>
        ts.isIdentifier(node) && node.text === "x" && ts.isReturnStatement(node.parent) ? node : node.forEachChild(find);
      const name = find(source);
      assert.ok(name);
      return { name, checker: p.checker };
    };
    const first = observed(() => open());
    assert.ok(first.observations.some(([o, p]) => o === "read" && p === file), "the compiler read the file");
    const { name, checker } = first.value;
    const before = queryTelemetry();
    // A record begun after the compiler read the file holds that read, by
    // the compiler's ledger, at its first request, asked or served.
    const asked = observed(() => checker.getSymbolAtLocation(name));
    const served = observed(() => checker.getSymbolAtLocation(name));
    const after = queryTelemetry();
    assert.equal(after.asked - before.asked, 2);
    assert.equal(after.served - before.served, 1, "the repeated query is served");
    for (const made of [asked, served])
      assert.ok(made.observations.some(([o, p]) => o === "read" && p === file), "a record using the compiler holds its ledger");
    assert.equal(asked.value?.name, served.value?.name);
    // Another snapshot's query is asked.
    const second = open();
    second.checker.getSymbolAtLocation(second.name);
    assert.equal(queryTelemetry().served, after.served, "another snapshot's query is asked");
    // Without sharing every query is asked.
    sharingForTests(false, () => second.checker.getSymbolAtLocation(second.name));
    assert.equal(queryTelemetry().served, after.served);
    // The compiler's incompleteness reaches every record that uses it.
    withLedger(compilerLedger(api), () => unobservable("an injected incomplete read"));
    const later = observed(() => second.checker.getSymbolAtLocation(second.name));
    assert.equal(later.incomplete, "an injected incomplete read");
  } finally {
    releaseCompiler(api, null);
  }
  process.stdout.write("query answers: served within a snapshot, asked across snapshots; a compiler's ledger in every record using it\n");
}
