import { execFileSync } from "node:child_process";
import { chmodSync, copyFileSync, mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join, resolve } from "node:path";
import { fieldOf } from "../tools/thrown.mts";

const repo = resolve(import.meta.dirname, "..");
const [version, directory = "_build/npm"] = process.argv.slice(2);
if (!version || !/^\d+\.\d+\.\d+(?:-[\w.-]+)?$/.test(version)) {
  throw Error("usage: node dev/pack-cli.mts VERSION [OUTPUT_DIR]");
}
if (process.platform !== "darwin" && process.platform !== "linux") {
  throw Error(`The CLI tarball supports macOS and Linux, received ${process.platform}`);
}

function manifestField(file: string, ...keys: string[]): string {
  let value: unknown = JSON.parse(readFileSync(join(repo, file), "utf8"));
  for (const key of keys) value = fieldOf(value, key);
  if (typeof value !== "string") throw Error(`Missing ${keys.join(".")} in ${file}`);
  return value;
}

const output = resolve(directory);
mkdirSync(output, { recursive: true });
const work = mkdtempSync(join(tmpdir(), "tscert-pack-"));
const artifact = join(work, "package");
try {
  const config = join(work, "tsconfig.json");
  writeFileSync(config, JSON.stringify({
    extends: join(repo, "tools/tsconfig.json"),
    compilerOptions: {
      noEmit: false, declaration: false, isolatedDeclarations: false,
      rewriteRelativeImportExtensions: true, rootDir: repo, outDir: artifact,
      typeRoots: [join(repo, "tools/node_modules/@types")],
    },
    include: [],
    files: [join(repo, "pipeline/verify-source.mts"), join(repo, "tools/resolvable.d.ts")],
  }));
  execFileSync(process.execPath, [join(repo, "tools/node_modules/typescript/bin/tsc"), "-p", config], { stdio: "inherit" });

  mkdirSync(join(artifact, "native"));
  copyFileSync(join(repo, "lean/.lake/build/bin/verifier"), join(artifact, "native/verifier"));
  copyFileSync(join(repo, "pipeline/runner/_build/stage-runner"), join(artifact, "native/stage-runner"));
  chmodSync(join(artifact, "pipeline/verify-source.mjs"), 0o755);
  copyFileSync(join(repo, "tools/resolvable.d.ts"), join(artifact, "tools/resolvable.d.ts"));
  copyFileSync(join(repo, "LICENSE"), join(artifact, "LICENSE"));
  copyFileSync(join(repo, "README.md"), join(artifact, "README.md"));

  writeFileSync(join(artifact, "package.json"), JSON.stringify({
    name: "@cristianoc/tscert",
    version,
    description: "Verify TypeScript type claims with TScert",
    license: "SEE LICENSE IN LICENSE",
    bin: { tscert: "pipeline/verify-source.mjs" },
    os: [process.platform],
    cpu: [process.arch],
    engines: { node: manifestField("package.json", "engines", "node") },
    dependencies: { typescript: manifestField("tools/package.json", "dependencies", "typescript") },
    exports: { "./effects": { types: "./tools/resolvable.d.ts" } },
  }, null, 2) + "\n");

  const name = execFileSync("npm", ["pack", "--pack-destination", work, "--cache", join(work, "cache"), "--loglevel=error"], {
    cwd: artifact, encoding: "utf8", stdio: ["ignore", "pipe", "inherit"],
  }).trim();
  const target = join(output, `tscert-${version}-${process.platform}-${process.arch}.tgz`);
  copyFileSync(join(work, name), target);
  console.log(target);
} finally {
  rmSync(work, { recursive: true, force: true });
}
