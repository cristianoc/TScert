// A file's bytes through the reviewed overlays: `readFileSync` without an
// encoding returns a fresh `Buffer`, read at the type the overlay of library
// types states, so its declaration, and `ArrayBufferLike` it names, are not
// read. A byte read by index is a number, or `undefined` past the end;
// `length`, `subarray` and `toString("utf8")`; `Buffer.from` of a string
// and `Buffer.compare` of two views; `update` of a hash with bytes.
import { createHash } from "node:crypto";
import { readFileSync } from "node:fs";

const sha256 = (bytes: string | Uint8Array): string =>
  createHash("sha256").update(bytes).digest("hex");
export function read(path: string): { bytes: Buffer; answer: string } {
  const bytes = readFileSync(path);
  return { bytes, answer: sha256(bytes) };
}
export function text(bytes: Buffer | null): string | undefined {
  return bytes === null ? undefined : bytes.toString("utf8");
}
export function first(bytes: Buffer): number {
  return bytes[0] ?? -1;
}
export function tail(bytes: Buffer): string {
  return bytes.subarray(1, bytes.length).toString("utf8");
}
export function size(bytes: Uint8Array): number {
  return bytes.length;
}
export function byBytes(a: string, b: string): number {
  return Buffer.compare(Buffer.from(a), Buffer.from(b));
}
export function digestOf(
  read: (module: string) => Buffer,
  module: string,
): string {
  const bytes = read(module);
  return createHash("sha256").update(bytes).digest("hex");
}
