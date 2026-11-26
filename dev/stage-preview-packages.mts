import { execFileSync } from "node:child_process";
import { copyFileSync, cpSync, mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join, resolve } from "node:path";
import { fieldOf } from "../tools/thrown.mts";

const [linux, macos, output] = process.argv.slice(2);
if (!linux || !macos || !output) {
  throw Error("usage: node dev/stage-preview-packages.mts LINUX.tgz MACOS.tgz OUTPUT_DIR");
}

function readManifest(directory: string): object {
  const path = join(directory, "package.json");
  const manifest: unknown = JSON.parse(readFileSync(path, "utf8"));
  if (!manifest || typeof manifest !== "object" || Array.isArray(manifest)) {
    throw Error(`Invalid package manifest at ${path}`);
  }
  return manifest;
}

const work = mkdtempSync(join(tmpdir(), "tscert-preview-"));
try {
  const targets = [
    { archive: linux, os: "linux", cpu: "x64" },
    { archive: macos, os: "darwin", cpu: "arm64" },
  ];
  for (const { archive, os, cpu } of targets) {
    const directory = join(work, `${os}-${cpu}`);
    mkdirSync(directory);
    execFileSync("tar", ["-xzf", resolve(archive), "-C", directory], { stdio: "inherit" });
  }
  const cli = join(work, "linux-x64/package");
  const manifest = readManifest(cli);
  const version = fieldOf(manifest, "version");
  const name = fieldOf(manifest, "name");
  const license = fieldOf(manifest, "license");
  if (typeof version !== "string" || typeof name !== "string" || typeof license !== "string") {
    throw Error("The CLI package must specify its version, name, and license");
  }
  const optionalDependencies: Record<string, string> = {};
  mkdirSync(output, { recursive: true });

  for (const { os, cpu } of targets) {
    const suffix = `${os}-${cpu}`;
    const source = join(work, suffix, "package");
    const platform = readManifest(source);
    if (fieldOf(platform, "name") !== name || fieldOf(platform, "version") !== version ||
        fieldOf(fieldOf(platform, "os"), "0") !== os || fieldOf(fieldOf(platform, "cpu"), "0") !== cpu) {
      throw Error(`Mismatched TScert package for ${suffix}`);
    }
    const platformName = `${name}-${suffix}`;
    const target = join(output, `tscert-${suffix}`);
    mkdirSync(target);
    for (const file of ["verifier", "stage-runner"]) {
      // Copy across filesystems and retain the executable mode from npm pack.
      const from = join(source, "native", file);
      const to = join(target, file);
      copyFileSync(from, to);
    }
    copyFileSync(join(source, "LICENSE"), join(target, "LICENSE"));
    writeFileSync(join(target, "package.json"), JSON.stringify({
      name: platformName, version, description: `TScert research preview binaries for ${suffix}`,
      license, os: [os], cpu: [cpu], files: ["verifier", "stage-runner"],
    }, null, 2) + "\n");
    optionalDependencies[platformName] = version;
  }

  rmSync(join(cli, "native"), { recursive: true });
  writeFileSync(join(cli, "package.json"), JSON.stringify({ ...manifest, os: undefined, cpu: undefined, optionalDependencies }, null, 2) + "\n");
  cpSync(cli, join(output, "tscert"), { recursive: true });
} finally {
  rmSync(work, { recursive: true, force: true });
}
