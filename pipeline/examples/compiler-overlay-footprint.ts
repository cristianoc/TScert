// Census functions: files.mts#compilerOverlay,#compilerFileSystem.
// Native map reads retain their checked effects through the live overlay.
import { compilerOverlay } from "../../tools/files.mts";

export function read(overlay: Map<string, string>, paths: string[]): string[] {
  const readers = compilerOverlay(overlay);
  return paths.map((path) => readers.get(path) ?? "");
}

export function live(): string {
  const overlay = new Map<string, string>();
  const readers = compilerOverlay(overlay);
  overlay.set("file.ts", "first");
  const first = readers.get("file.ts") ?? "";
  overlay.set("file.ts", "second");
  return first + ":" + readers.get("file.ts");
}
