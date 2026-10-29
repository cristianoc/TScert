// Node's resolution, its conditions and a module's load run through the host
// boundary tools/module-hooks.mts, as files.mts uses them: the program
// receives URLs, conditions, the reads a load made and its outcome as plain
// values, and holds no hook.
// Census functions: files.mts#resolveObserved, files.mts#runtimeConditions,
// files.mts#loadModule.
import { isBuiltin } from "node:module";
import { loadObserved, resolutionConditions, resolveWithNode } from "../../tools/module-hooks.mts";

export function resolved(specifier: string, parentHref: string): string | null {
  if (isBuiltin(specifier)) return null;
  const url = resolveWithNode(specifier, parentHref);
  return url !== null && url.startsWith("file:") ? url : null;
}

export function conditions(): string[] {
  return [...resolutionConditions(), "default"];
}

export function load(path: string): { files: string[]; value: unknown } {
  const { reads, outcome } = loadObserved(path);
  const files: string[] = [];
  for (const { url, digest } of reads) {
    if (url === null || url.startsWith("node:")) continue;
    files.push(digest === null ? url : `${url} ${digest}`);
  }
  if (outcome.k === "threw") throw outcome.thrown;
  return { files, value: outcome.value };
}
