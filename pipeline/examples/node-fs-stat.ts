// `statSync` at a string path returns a fresh `Stats` owning its numbers;
// an `is…` test returns an unknown value, a condition, or a Boolean once
// compared with `true`. `mkdirSync` with `recursive: true`, `writeFileSync`
// with a mode and `chmodSync` at a number: all through the reviewed
// overlay, so `Buffer`, which `PathLike` names, is not read.
import { chmodSync, mkdirSync, statSync, writeFileSync } from "node:fs";

export function kind(path: string): "directory" | "file" {
  return statSync(path).isDirectory() ? "directory" : "file";
}
export function installed(path: string): boolean {
  try {
    return statSync(path).isFile() === true;
  } catch {
    return false;
  }
}
export function signature(path: string): string {
  const s = statSync(path);
  s.size = s.size + 1;
  return `${s.dev}:${s.ino}:${s.size}:${s.mtimeMs}`;
}
export function launcher(
  directory: string,
  path: string,
  text: string,
): string | undefined {
  const made = mkdirSync(directory, { recursive: true });
  writeFileSync(path, text, { mode: 0o500 });
  chmodSync(path, 0o500);
  return made;
}
