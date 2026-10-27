// `statSync(path).size` through `statSync`'s reviewed entry: its declaration,
// which reaches `Buffer` through `PathLike`, is not read. A file's bytes
// through `readFileSync`'s, a `Buffer`, read at the type the overlay of
// library types states: its declaration, which names the conditional type
// `ImplicitArrayBuffer`, is not read either.
// Census functions:
// family-activation.mts#declarationInventory, files.mts#attemptAnswer,
// files.mts#byBytes, files.mts#compilerText, files.mts#findPackage,
// files.mts#installed, files.mts#kindOf, files.mts#manifestField,
// files.mts#observeScope, files.mts#privateLauncher, files.mts#readAnswer,
// files.mts#readBytes, files.mts#realOf, files.mts#realPath,
// guard-closure.mts#guardClosure.
import { readFileSync, statSync } from "node:fs";
export function use(path: string): number {
  return statSync(path).size;
}
export function manifestField(bytes: Buffer | null): unknown {
  if (bytes === null) return undefined;
  return JSON.parse(bytes.toString("utf8"));
}
export function readBytes(path: string): Buffer {
  return readFileSync(path);
}
export function byBytes(a: string, b: string): number {
  return Buffer.compare(Buffer.from(a), Buffer.from(b));
}
export function compilerText(bytes: Buffer): string {
  return new TextDecoder("utf-8", { fatal: true }).decode(
    bytes.subarray(bytes[0] === 0xef ? 3 : 0),
  );
}
