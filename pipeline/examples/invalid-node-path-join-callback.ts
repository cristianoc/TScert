// A replacement for the standard normalizer shrinks map's input, leaving
// a hole under Node. Access to that native implementation object is refused.
import path, { join } from "node:path";

export function tamper(files: string[]): void {
  const normalize = path.posix.normalize;
  path.posix.normalize = (p: string): string => {
    files.pop();
    return normalize(p);
  };
}

export function parents(files: string[]): string[] {
  return files.map((f) => join(f, ".."));
}
