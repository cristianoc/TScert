// Test-only native mutations. All compiler outputs live in the run directory;
// the verifier, Lean sources and Lake cache are read-only inputs.
import assert from "node:assert/strict";
import { readFileSync, writeFileSync } from "node:fs";
import { join, resolve } from "node:path";
import { present } from "../tools/files.mts";
import { spawnSync } from "node:child_process";
import { tested } from "./stages.mts";
import { auditMutationVerifier, verifierCall } from "./stage-execution.mts";
import { sourceKey } from "./verify-source.mts";
import { runDirectory } from "./run-directory.mts";

const lean = resolve(import.meta.dirname, "../lean");
const prefix = "lp_verification_Verification_";
// The executable this process uses; null where it uses only one another process
// builds and has none yet.
let executable: string | null | undefined;

function command(program: string, args: string[]): string {
  const result = spawnSync(program, args, { cwd: lean, encoding: "utf8", timeout: 180_000 });
  assert.ifError(result.error);
  assert.equal(result.status, 0, result.stdout + result.stderr);
  return result.stdout.trim();
}

// Locate a definition by its Lean symbol, and bind its arguments by position.
// Compiler-local variable numbers are deliberately not part of the recipe.
function inject(source: string, symbol: string, body: (args: string[]) => string): string {
  const pattern = new RegExp(`LEAN_EXPORT [^\\n]+ ${prefix}${symbol}\\(([^;\\n]*)\\)\\{`, "g");
  const matches = [...source.matchAll(pattern)];
  assert.equal(matches.length, 1, `one C definition of ${symbol}`);
  const match = matches[0];
  const args = match[1].split(",").map(a => a.trim().split(/\s+/).at(-1) ?? "");
  const at = match.index + match[0].length;
  return source.slice(0, at) + "\n" + body(args) + "\n" + source.slice(at);
}

const header = `
extern char *getenv(const char *);
extern char *strstr(const char *, const char *);
extern void abort(void);
extern lean_object *lp_verification_Verification_HeapKnowledge_shift(lean_object *);
static int mutation(const char *name) {
  const char *m = getenv("TSCERT_TEST_MUTATIONS");
  return m && strstr(m, name);
}
static lean_object *pair(lean_object *a, lean_object *b) {
  lean_object *r = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(r, 0, a); lean_ctor_set(r, 1, b); return r;
}
static lean_object *some(lean_object *a) {
  lean_object *r = lean_alloc_ctor(1, 1, 0); lean_ctor_set(r, 0, a); return r;
}
`;

/** Build a separate executable from the current build's C, with opt-in mutations.
 * No mutation flag is compiled into the production verifier. Its modules
 * compile at once; the link is the build's own. A process builds it once,
 * or uses the one `useMutationVerifier` names. */
export function mutationVerifier(): string {
  if (executable) return executable;
  if (executable === null) throw Error("this process runs the mutation verifier another process builds, and has none yet");
  const dir = runDirectory("evidence-mutations-");
  const compiles: { c: string; args: string[] }[] = [];
  const toolchain = command("lean", ["--print-prefix"]);
  const clang = join(toolchain, "bin", "clang");
  let response = readFileSync(join(lean, ".lake/build/bin/verifier.rsp"), "utf8");
  const modules = ["Programs/PointClaims", "Programs/BranchRefinement", "Semantics/HeapLinks", "Semantics/HeapSeparation",
    "Semantics/HeapKnowledge", "Semantics/KnowledgeExpand", "Programs/HeapExpressionRules", "Programs/ControlFlow", "Programs/CertificateProducer",
    "Programs/ExpressionEffects", "Source/RequestJson", "Source/Lowering/ClosureSetup"];
  for (const module of modules) {
    const original = join(lean, ".lake/build/ir/Verification", `${module}.c`);
    let text = readFileSync(original, "utf8");
    if (module === "Programs/PointClaims" || module === "Programs/BranchRefinement") {
      const symbol = module.endsWith("PointClaims") ? "PointClaims_checkMappedResult___redArg" : "BranchRefinement_checkObservedResult___redArg";
      text = inject(text, symbol, () => 'if (mutation("coverage")) return pair(some(lean_box(0)), lean_box(0));');
    }
    if (module === "Semantics/HeapLinks")
      for (const symbol of ["HeapLinks_check", "HeapLinks_checkWith"])
        text = inject(text, symbol, () => 'if (mutation("links")) return 1;');
    if (module === "Semantics/HeapSeparation")
      for (const symbol of ["HeapSeparation_check", "HeapSeparation_checkAgainst"])
        text = inject(text, symbol, () => 'if (mutation("separation")) return 1;');
    if (module === "Semantics/HeapKnowledge") {
      // Only the heap-cell conjunct; immutable value facts remain checked.
      const pattern = /(v_\w+) = (lp_verification_List_all___at___00Verification_HeapFacts_check_spec__1\(v_\w+, v_cells_\w+, v_cells_\w+\));/g;
      assert.equal([...text.matchAll(pattern)].length, 1);
      text = text.replace(pattern, '$1 = mutation("cells") ? 1 : $2;');
    }
    // The edge check against a stored normal form (`KnowledgeExpand.checkIn`).
    if (module === "Semantics/KnowledgeExpand")
      text = inject(text, "KnowledgeExpand_cellsCheck", () => 'if (mutation("cells")) return 1;');
    if (module === "Programs/HeapExpressionRules") {
      text = inject(text, "HeapExpressionRules_stableLinks___redArg", a => `if (mutation("stable")) { lean_object *r = lean_ctor_get(${a[2]}, 2); lean_inc(r); return r; }`);
      // A read a cell fact answers: its link optional whatever the receiver's
      // type states (`read-observed-present` withheld).
      text = inject(text, "HeapExpressionRules_readOutput", a => `if (mutation("absent")) ${a[4]} = 1;`);
    }
    if (module === "Programs/ControlFlow")
      text = inject(text, "ControlFlow_handlerFacts", a => `if (mutation("handler")) {
        lean_object *k = lean_alloc_ctor(0, 4, 0);
        lean_ctor_set(k, 0, lean_box(0));
        lean_object *values = lean_ctor_get(${a[0]}, 1), *links = lean_ctor_get(${a[0]}, 2);
        lean_object *separation = lean_ctor_get(${a[0]}, 3);
        lean_inc(values); lean_inc(links); lean_inc(separation);
        lean_ctor_set(k, 1, values); lean_ctor_set(k, 2, links); lean_ctor_set(k, 3, separation);
        return ${prefix}HeapKnowledge_shift(k);
      }`);
    if (module === "Programs/ControlFlow") {
      const start = text.indexOf(`LEAN_EXPORT lean_object* ${prefix}ControlFlow_checkHandlerResult___redArg___lam__0(lean_object* v_`);
      assert.ok(start >= 0);
      const end = text.indexOf("\nLEAN_EXPORT", start + 1);
      const part = text.slice(start, end);
      assert.equal(part.split(`${prefix}HeapExpressionRules_ordinaryOutput(`).length, 2);
      text = text.slice(0, start) + part.replace(`${prefix}HeapExpressionRules_ordinaryOutput(`,
        `${prefix}ControlFlow_handlerFacts(`) + text.slice(end);
    }
    if (module === "Programs/CertificateProducer")
      text = inject(text, "CertificateProducer_edgeUsing___redArg", a => `if (mutation("coverage")) {
        lean_object *cs = ${a[5]}; size_t n = lean_unbox(lean_ctor_get(${a[7]}, 0));
        while (n-- && !lean_is_scalar(cs)) cs = lean_ctor_get(cs, 1);
        if (lean_is_scalar(cs)) abort();
        lean_object *context = lean_ctor_get(lean_ctor_get(cs, 0), 0), *proofs = lean_box(0);
        while (!lean_is_scalar(context)) {
          lean_object *cons = lean_alloc_ctor(1, 2, 0);
          lean_ctor_set(cons, 0, pair(lean_box(0), lean_box(0))); lean_ctor_set(cons, 1, proofs);
          proofs = cons; context = lean_ctor_get(context, 1);
        }
        return pair(pair(some(proofs), lean_box(0)), ${a[12]});
      }`);
    // Every type decided empty: a node at any type taken never to return
    // normally (`no-return`'s premise removed).
    if (module === "Programs/ExpressionEffects")
      text = inject(text, "ExpressionEffects_emptyType___redArg", () => 'if (mutation("empty")) return 1;');
    // An async definition's footprint below `top` admitted (L6 removed).
    if (module === "Source/RequestJson")
      text = inject(text, "RequestJson_asyncEffects", () => 'if (mutation("async")) return 1;');
    // A stated declaration's claim admitted outside its statement, and a
    // stated closure's code not required to cover its statement (L2
    // removed).
    if (module === "Source/RequestJson")
      text = inject(text, "RequestJson_statedWithin", () => 'if (mutation("stated")) return 1;');
    if (module === "Source/Lowering/ClosureSetup")
      text = inject(text, "SourceExtraction_statedObligation", () => 'if (mutation("stated")) return lean_box(0);');
    const c = join(dir, module.replaceAll("/", "-") + ".c");
    const o = c + ".o";
    writeFileSync(c, text.replace("#include <lean/lean.h>", "#include <lean/lean.h>\n" + header));
    compiles.push({ c, args: ["-c", c, "-o", o, "-I", join(toolchain, "include"), "--sysroot", toolchain,
      "-nostdinc", "-isystem", join(toolchain, "include/clang"), "-O1", "-DNDEBUG", "-DLEAN_EXPORTING"] });
    assert.ok(response.includes(JSON.stringify(original + ".o.export")));
    response = response.replace(JSON.stringify(original + ".o.export"), JSON.stringify(o));
  }
  // Each module its own clang process, all at once.
  const quote = (text: string): string => `'${text.replace(/'/g, `'\\''`)}'`;
  const script = compiles.map(({ c, args }) => `${[clang, ...args].map(quote).join(" ")} > ${quote(c + ".log")} 2>&1 & p="$p $!"`)
    .join("\n") + "\ns=0\nfor q in $p; do wait $q || s=1; done\nexit $s\n";
  const compiled = spawnSync("/bin/sh", ["-c", script], { cwd: lean, encoding: "utf8", timeout: 180_000 });
  assert.ifError(compiled.error);
  assert.equal(compiled.status, 0, compiles.map(({ c }) => present(c + ".log") ? readFileSync(c + ".log", "utf8") : "").join(""));
  const rsp = join(dir, "mutation.rsp");
  writeFileSync(rsp, response);
  executable = join(dir, "mutation-verifier");
  command(clang, ["-o", executable, "@" + rsp]);
  auditMutationVerifier(executable);
  return executable;
}

/** Use the mutation verifier at `path`, which another process of this run
 * built from the same build (`pipeline/test.mts`'s control processes); with
 * null, build none in this process. */
export function useMutationVerifier(path: string | null): void {
  if (path !== null) auditMutationVerifier(path);
  executable = path;
}

/** Require acceptance under the selected mutation and refusal with each
 * selected component removed. This checks that every bypass is necessary. */
export function checkMutation(artifacts: string, claims: string, path: string, mutations: string): void {
  const selected = mutations.split(",");
  const variants = [mutations, ...selected.map(removed => selected.filter(m => m !== removed).join(","))];
  if (mutations === "stable") variants.push("handler");
  if (mutations === "handler") variants.push("stable");
  for (const [i, variant] of variants.entries()) {
    const result = tested(verifierCall(mutationVerifier(), ["--check-source-claims", join(artifacts, "fragment.json"),
      claims, sourceKey(artifacts), path], { TSCERT_TEST_MUTATIONS: variant }));
    assert.ifError(result.error);
    assert.equal(result.status, i === 0 ? 0 : 1,
      `${path}, mutation ${variant || "none"}: ${result.stdout}${result.stderr}`);
  }
}

/** Generate evidence from source-anchored claims, then validate that exact
 * document under the intended mutation and its component-removal controls. */
export function forgedEvidence(artifacts: string, claims: string, name: string, mutations: string): string {
  const path = join(artifacts, `${name}-generated.json`);
  const result = tested(verifierCall(mutationVerifier(), ["--produce-source-claims", join(artifacts, "fragment.json"),
    claims, sourceKey(artifacts), path, "12"], { TSCERT_TEST_MUTATIONS: mutations }));
  assert.ifError(result.error);
  assert.equal(result.status, 0, `${name}, ${mutations}: ${result.stdout}${result.stderr}`);
  checkMutation(artifacts, claims, path, mutations);
  return path;
}

// The build alone, its executable's path printed: for a suite that builds it
// once beside its other work.
if (import.meta.filename === resolve(process.argv[1] ?? "") && process.argv[2] === "--build")
  process.stdout.write(mutationVerifier() + "\n");
