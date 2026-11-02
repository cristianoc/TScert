// `node:path`'s `dirname` and `basename` at strings run no code of the
// client's and allocate only the string they return, so a `map` callback
// calling them stays within the empty footprint and its result dense;
// `join` also preserves stores under untampered standard objects;
// `resolve`, `relative` and `realpathSync` are called outside the maps.
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

// Mapping through join while the standard normalizer is untampered.
export function joinedParents(files: string[]): string[] {
  return files.map((f) => join(f, ".."));
}
