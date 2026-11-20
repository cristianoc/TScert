// A verifier whose single pass (`Programs/SinglePass.lean`) and framed
// plans' checks have opt-in mutations, for the controls showing each check is what
// refuses some unit (tests/single-pass-controls.mts). Built from the current
// build's generated C of the pass's module and of the module its generic
// code is specialized into (`Source/Claims/Json`, the file plans), a
// mutation injected at the entry of each definition of the check, its
// specializations included, compiled and linked by the build's own
// link response; the verifier, Lean sources and Lake cache are read-only
// inputs. A mutation is selected by `TSCERT_TEST_MUTATIONS` (a list of
// names), which the invocation's environment fixes, so it is part of the
// stage key; no mutation is compiled into the production verifier.
//   sp-entry       `SinglePass.entryRefusal`: the start's entry refuses nothing
//   sp-footprint   `SinglePass.footprintCheck`: every unit's footprint holds
//   sp-edge-evidence  `SinglePass.edgeEvidenceChecked`: every edge's slot evidence is accepted
//   fr-protected   `SourceClaimJson.protRegionB`: every region of a framed node is read as protected
//   fr-ro-sharing  `SourceClaimJson.sharingReadOnlyB`: a position is read-only where the member declares it
import assert from "node:assert/strict";
import { chmodSync, readFileSync, writeFileSync } from "node:fs";
import { randomUUID } from "node:crypto";
import { join, resolve } from "node:path";
import { spawnSync } from "node:child_process";
import { auditMutationVerifier, canonical, sha256, verifierBuild } from "../pipeline/stage-execution.mts";
import { currentStore } from "../pipeline/stages.mts";
import { runDirectory } from "../pipeline/run-directory.mts";

const lean = resolve(import.meta.dirname, "../lean");
const prefix = "lp_verification_Verification_";

function command(program: string, args: string[]): string {
  const result = spawnSync(program, args, { cwd: lean, encoding: "utf8", timeout: 300_000 });
  assert.ifError(result.error);
  assert.equal(result.status, 0, result.stdout + result.stderr);
  return result.stdout.trim();
}

/** `source` with `body` at the entry of every C definition of the check
 * `name` (its namespace's components joined by `_`): the generic one, its
 * reduced form and its specializations (`___at___…`); none of the boxed
 * wrappers or lambdas. The count injected. */
function inject(source: string, name: string, body: string): { text: string; count: number } {
  const pattern = new RegExp(`LEAN_EXPORT [^\\n]+ ${prefix}${name}(?:___redArg)?(?:___at___[A-Za-z0-9_]*?)?\\(([^;\\n]*)\\)\\{`, "g");
  const matches = [...source.matchAll(pattern)].filter((m) => !/___boxed\(|___lam__/.test(m[0]));
  let text = source;
  for (const match of matches.reverse()) {
    const at = match.index + match[0].length;
    text = text.slice(0, at) + "\n" + body + "\n" + text.slice(at);
  }
  return { text, count: matches.length };
}

const header = `
extern char *getenv(const char *);
extern char *strstr(const char *, const char *);
static int mutation(const char *name) {
  const char *m = getenv("TSCERT_TEST_MUTATIONS");
  return m && strstr(m, name);
}
`;

/** The mutations, each the definitions it is injected into and what it
 * returns there: a Boolean check's success (1), or an absent refusal. */
export const passMutations: readonly { name: string; check: string; returns: string }[] = [
  { name: "sp-entry", check: "SinglePass_entryRefusal", returns: "lean_box(0)" },
  { name: "sp-footprint", check: "SinglePass_footprintCheck", returns: "1" },
  { name: "sp-edge-evidence", check: "SinglePass_edgeEvidenceChecked", returns: "1" },
  { name: "fr-protected", check: "SourceClaimJson_protRegionB", returns: "1" },
  { name: "fr-ro-sharing", check: "SourceClaimJson_sharingReadOnlyB", returns: "1" },
];

/** The modules whose generated C holds the mutated checks' definitions:
 * the pass's, the file plans' its generic code is specialized into, and
 * the framed plans' checks. */
const mutatedModules = ["Programs/SinglePass", "Source/Claims/Json", "Source/Claims/FramedNodeChecks",
  "Source/Claims/FramedPassChecks"];

/** Build the mutation verifier of the pass in `dir` (a run directory of
 * this process's by default); its path. */
export function passMutationVerifier(dir: string = runDirectory("single-pass-mutations-")): string {
  const toolchain = command("lean", ["--print-prefix"]);
  const clang = join(toolchain, "bin", "clang");
  let response = readFileSync(join(lean, ".lake/build/bin/verifier.rsp"), "utf8");
  const counts = new Map<string, number>();
  for (const module of mutatedModules) {
    const original = join(lean, ".lake/build/ir/Verification", `${module}.c`);
    let text = readFileSync(original, "utf8");
    for (const m of passMutations) {
      const injected = inject(text, m.check, `if (mutation("${m.name}")) return ${m.returns};`);
      text = injected.text;
      counts.set(m.name, (counts.get(m.name) ?? 0) + injected.count);
    }
    const c = join(dir, `${module.replaceAll("/", "-")}.c`), o = c + ".o";
    writeFileSync(c, text.replace("#include <lean/lean.h>", "#include <lean/lean.h>\n" + header));
    const compiled = spawnSync(clang, ["-c", c, "-o", o, "-I", join(toolchain, "include"), "--sysroot", toolchain,
      "-nostdinc", "-isystem", join(toolchain, "include/clang"), "-O0", "-DNDEBUG", "-DLEAN_EXPORTING"],
      { cwd: lean, encoding: "utf8", timeout: 600_000 });
    assert.ifError(compiled.error);
    assert.equal(compiled.status, 0, compiled.stdout + compiled.stderr);
    assert.ok(response.includes(JSON.stringify(original + ".o.export")), `the link response names ${module}'s object`);
    response = response.replace(JSON.stringify(original + ".o.export"), JSON.stringify(o));
  }
  for (const m of passMutations) assert.ok((counts.get(m.name) ?? 0) > 0, `${m.name}: a definition of ${m.check}`);
  const rsp = join(dir, "mutation.rsp");
  writeFileSync(rsp, response);
  const executable = join(dir, "single-pass-mutation-verifier");
  command(clang, ["-o", executable, "@" + rsp]);
  auditMutationVerifier(executable);
  return executable;
}

/** The mutation verifier in `dir`, replayed from the stage store where it
 * holds a build from the same inputs: the verifier's executable, the
 * generated C of the pass's modules and the link response, by content, the
 * toolchain and this module's source. Lean's build changing any of them
 * builds it again and publishes it under the new key (entry
 * `mutation-verifier/<key>`); with the store off it is built every time. */
export function cachedPassMutationVerifier(dir: string): string {
  const store = currentStore();
  const executable = join(dir, "single-pass-mutation-verifier");
  const ir = (module: string): string => sha256(readFileSync(join(lean, ".lake/build/ir/Verification", `${module}.c`)));
  const input = canonical({ mutations: sha256(readFileSync(import.meta.filename)), verifier: sha256(readFileSync(verifierBuild)),
    modules: mutatedModules.map(ir),
    link: sha256(readFileSync(join(lean, ".lake/build/bin/verifier.rsp"))), toolchain: command("lean", ["--print-prefix"]) });
  const key = sha256(input);
  const found = store?.finished("mutation-verifier", key, input)?.result.outputs.find(([role]) => role === "verifier")?.[1];
  if (found !== undefined) {
    writeFileSync(executable, found);
    chmodSync(executable, 0o755);
    auditMutationVerifier(executable);
    return executable;
  }
  const started = performance.now();
  const built = passMutationVerifier(dir);
  store?.publishFinished("mutation-verifier", key, { input, exitStatus: 0, stdout: Buffer.alloc(0), stderr: Buffer.alloc(0),
    outputs: [["verifier", readFileSync(built)]], measurement: { attempt: randomUUID(), elapsedMs: performance.now() - started,
      limitMs: null, cpu: { unavailable: "a build of the mutation verifier" } } });
  return built;
}

/** Use the mutation verifier at `path`, which the suite's process built. */
export function usePassMutationVerifier(path: string): string {
  auditMutationVerifier(path);
  return path;
}

// `node tests/single-pass-mutations.mts --build <dir>`: build it in `dir`, a
// directory the caller owns, or replay its build from the store, and print
// its path.
if (process.argv[1] === import.meta.filename && process.argv[2] === "--build" && process.argv[3] !== undefined)
  process.stdout.write(`${cachedPassMutationVerifier(process.argv[3])}\n`);
