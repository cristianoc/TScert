// Test-only native mutations. All compiler outputs live in the run directory;
// the verifier, Lean sources and Lake cache are read-only inputs.
import assert from "node:assert/strict";
import { chmodSync, existsSync, readdirSync, readFileSync, realpathSync, statSync, writeFileSync } from "node:fs";
import { createHash } from "node:crypto";
import { join, resolve } from "node:path";
import { spawnSync } from "node:child_process";
import { currentStore, forced, linkedLibraries, verifierCall } from "./stages.mts";
import { sourceKey } from "./verify-source.mts";
import { runDirectory } from "./run-directory.mts";

const lean = resolve(import.meta.dirname, "../lean");
const prefix = "lp_verification_Verification_";
let executable: string | undefined;

function command(program: string, args: string[], env?: Record<string, string>): string {
  const result = spawnSync(program, args, { cwd: lean, env, encoding: "utf8", timeout: 180_000 });
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

/** Digest the bounded native build inputs, following symlinks by content. */
function buildFiles(paths: string[]): [string, string][] {
  return paths.sort().flatMap((path) => {
    if (!existsSync(path)) return [[path, "absent"]];
    if (statSync(path).isDirectory())
      return buildFiles(readdirSync(path).map((name) => join(path, name)));
    return [[path, createHash("sha256").update(readFileSync(path)).digest("hex")]];
  });
}

/** The supported Lake link recipe has explicit objects, search directories
 * and libraries. Refuse other flags so new build inputs require an audit. */
function linkInputs(response: string, toolchain: string): string[] {
  const tokens = response.trim().split("\n").map((line) => {
    const value: unknown = JSON.parse(line);
    assert.ok(typeof value === "string");
    return value;
  });
  const paths: string[] = [];
  const directories: string[] = [];
  const libraries = ["System"];
  for (let i = 0; i < tokens.length; i++) {
    const token = tokens[i];
    if (token === "-L") {
      const directory = tokens[++i];
      assert.ok(directory);
      directories.push(resolve(lean, directory));
    } else if (token === "--sysroot") {
      assert.equal(tokens[++i], toolchain);
    } else if (/^-l[A-Za-z0-9_+]+$/.test(token)) {
      libraries.push(token.slice(2));
    } else if (token === "-fuse-ld=lld" || token === "-Wl,-dead_strip") {
      continue;
    } else {
      assert.ok(!token.startsWith("-") && /\.(c|o|o\.export)$/.test(token), `unsupported mutation link input: ${token}`);
      paths.push(resolve(lean, token));
    }
  }
  for (const library of libraries) {
    // Bind every candidate, including absence, so changes in search order
    // and newly introduced higher-priority files are covered.
    const candidates = directories.flatMap((directory) =>
      ["tbd", "dylib", "a"].map((suffix) => join(directory, `lib${library}.${suffix}`)));
    assert.ok(candidates.some((path) => existsSync(path)), `unresolved library: ${library}`);
    paths.push(...candidates);
  }
  return paths;
}

/** Build an isolated executable with opt-in mutations. The store key covers
 * the supported link recipe, its library candidates, headers, compiler and
 * linker with their dynamic dependencies, and the explicit build environment. */
export function mutationVerifier(): string {
  if (executable) return executable;
  const dir = runDirectory("evidence-mutations-");
  const toolchain = command("lean", ["--print-prefix"]);
  const clang = join(toolchain, "bin", "clang");
  const linker = join(toolchain, "bin", "ld64.lld");
  const env = { PATH: "/usr/bin:/bin", TMPDIR: dir, LC_ALL: "C", SOURCE_DATE_EPOCH: "0" };
  const nativeArgs = ["--no-default-config", "-nostdinc", "-I", join(toolchain, "include"),
    "-isystem", join(toolchain, "include/clang")];
  const compiles: { c: string; text: string; args: string[] }[] = [];
  let response = readFileSync(join(lean, ".lake/build/bin/verifier.rsp"), "utf8");
  const modules = ["Programs/PointClaims", "Programs/BranchRefinement", "Semantics/HeapLinks",
    "Semantics/HeapKnowledge", "Programs/HeapExpressionRules", "Programs/ControlFlow", "Programs/CertificateProducer"];
  for (const module of modules) {
    const original = join(lean, ".lake/build/ir/Verification", `${module}.c`);
    let text = readFileSync(original, "utf8");
    if (module === "Programs/PointClaims" || module === "Programs/BranchRefinement") {
      const symbol = module.endsWith("PointClaims") ? "PointClaims_checkMappedResult___redArg" : "BranchRefinement_checkObservedResult___redArg";
      text = inject(text, symbol, () => 'if (mutation("coverage")) return pair(some(lean_box(0)), lean_box(0));');
    }
    if (module === "Semantics/HeapLinks")
      text = inject(text, "HeapLinks_check", () => 'if (mutation("links")) return 1;');
    if (module === "Semantics/HeapKnowledge") {
      // Only the heap-cell conjunct; immutable value facts remain checked.
      const pattern = /(v_\w+) = (lp_verification_List_all___at___00Verification_HeapFacts_check_spec__1\(v_\w+, v_cells_\w+, v_cells_\w+\));/g;
      assert.equal([...text.matchAll(pattern)].length, 1);
      text = text.replace(pattern, '$1 = mutation("cells") ? 1 : $2;');
    }
    if (module === "Programs/HeapExpressionRules")
      text = inject(text, "HeapExpressionRules_stableLinks___redArg", a => `if (mutation("stable")) { lean_object *r = lean_ctor_get(${a[2]}, 2); lean_inc(r); return r; }`);
    if (module === "Programs/ControlFlow")
      text = inject(text, "ControlFlow_handlerFacts", a => `if (mutation("handler")) {
        lean_object *k = lean_alloc_ctor(0, 3, 0);
        lean_ctor_set(k, 0, lean_box(0));
        lean_object *values = lean_ctor_get(${a[0]}, 1), *links = lean_ctor_get(${a[0]}, 2);
        lean_inc(values); lean_inc(links); lean_ctor_set(k, 1, values); lean_ctor_set(k, 2, links);
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
    const c = join(dir, module.replaceAll("/", "-") + ".c");
    const o = c + ".o";
    compiles.push({ c, text: text.replace("#include <lean/lean.h>", "#include <lean/lean.h>\n" + header),
      args: [...nativeArgs, "-c", c, "-o", o, "--sysroot", toolchain, "-O1", "-DNDEBUG", "-DLEAN_EXPORTING"] });
    assert.ok(response.includes(JSON.stringify(original + ".o.export")));
    response = response.replace(JSON.stringify(original + ".o.export"), JSON.stringify(o));
  }
  const inputs = linkInputs(response, toolchain).filter((path) => !compiles.some((c) => path === c.c + ".o"));
  // Clang's resource tree includes its builtin runtime archive. Standard
  // search paths and default libraries are disabled in the actual link.
  const resource = command(clang, ["--no-default-config", "-print-resource-dir"], env);
  const runtime = join(resource, "lib/darwin/libclang_rt.osx.a");
  const linkArgs = [...nativeArgs, "--ld-path=" + linker, "-nostdlib", "-Wl,-Z", "-lSystem", runtime];
  const dependencies = [clang, linker, "/bin/sh"].map((program) => {
    const libraries = linkedLibraries(program);
    assert.ok(typeof libraries !== "string", `${program}: ${String(libraries)}`);
    return [realpathSync(program), libraries];
  });
  const named = buildFiles([...inputs, clang, linker, join(toolchain, "include"), resource]);
  // Temporary output paths have no semantic role in these commands.
  const key = createHash("sha256").update(JSON.stringify({ toolchain, header, dependencies,
    env: { ...env, TMPDIR: "<dir>" }, linkArgs,
    compiles: compiles.map((c) => [c.text, c.args.map((a) => a.replaceAll(dir, "<dir>"))]),
    response: response.replaceAll(dir, "<dir>"), named })).digest("hex");
  executable = join(dir, "mutation-verifier");
  const store = currentStore();
  if (store?.copyBuilt("mutation-verifier", key, "mutation-verifier", executable)) {
    chmodSync(executable, 0o755);
    return executable;
  }
  for (const { c, text } of compiles) writeFileSync(c, text);
  // The modules compile at once, each its own clang process.
  const quote = (text: string): string => `'${text.replace(/'/g, `'\\''`)}'`;
  const script = compiles.map(({ c, args }) => `${[clang, ...args].map(quote).join(" ")} > ${quote(c + ".log")} 2>&1 & p="$p $!"`)
    .join("\n") + "\ns=0\nfor q in $p; do wait $q || s=1; done\nexit $s\n";
  const compiled = spawnSync("/bin/sh", ["-c", script], { cwd: lean, env, encoding: "utf8", timeout: 180_000 });
  assert.ifError(compiled.error);
  assert.equal(compiled.status, 0, compiles.map(({ c }) => {
    try {
      return readFileSync(c + ".log", "utf8");
    } catch {
      return "";
    }
  }).join(""));
  const rsp = join(dir, "mutation.rsp");
  writeFileSync(rsp, response);
  command(clang, ["-o", executable, "@" + rsp, ...linkArgs], env);
  store?.publishBuilt("mutation-verifier", key, "mutation-verifier", executable);
  return executable;
}

/** Require acceptance under the selected mutation and refusal with each
 * selected component removed. This checks that every bypass is necessary. */
export function checkMutation(artifacts: string, claims: string, path: string, mutations: string): void {
  const selected = mutations.split(",");
  const variants = [mutations, ...selected.map(removed => selected.filter(m => m !== removed).join(","))];
  if (mutations === "stable") variants.push("handler");
  if (mutations === "handler") variants.push("stable");
  for (const [i, variant] of variants.entries()) {
    const result = forced(verifierCall(mutationVerifier(), ["--check-source-claims", join(artifacts, "fragment.json"),
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
  const result = forced(verifierCall(mutationVerifier(), ["--produce-source-claims", join(artifacts, "fragment.json"),
    claims, sourceKey(artifacts), path, "12"], { TSCERT_TEST_MUTATIONS: mutations }));
  assert.ifError(result.error);
  assert.equal(result.status, 0, `${name}, ${mutations}: ${result.stdout}${result.stderr}`);
  checkMutation(artifacts, claims, path, mutations);
  return path;
}
