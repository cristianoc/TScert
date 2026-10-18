// `node:path`'s `dirname` and `basename` at strings run no code of the
// client's and allocate only the string they return, so a `map` callback
// calling them stays within the empty footprint and its result dense;
// `join`, `resolve`, `relative` and `realpathSync` are called outside it.
import { realpathSync } from "node:fs";
import { basename, dirname, join, relative, resolve } from "node:path";

export function parents(files: string[]): string[] {
  return files.map((f) => dirname(f));
}

export function names(files: string[]): string[] {
  return files.map((f) => basename(f, ".ts"));
}

export function under(root: string, file: string): string {
  return relative(realpathSync(root), resolve(join(root, "."), file));
}
