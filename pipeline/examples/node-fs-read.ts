// `node:fs`'s `readFileSync` at a string path and the encoding "utf8"
// returns the file's text, and `existsSync` at a string path a Boolean:
// both read through the reviewed overlay, so `Buffer`, which the
// declarations of their other forms name, is not read.
import { existsSync, readFileSync } from "node:fs";

export function text(file: string): string {
  return existsSync(file) ? readFileSync(file, "utf8") : "";
}
export function lines(file: string): number {
  return readFileSync(file, "utf8").split("\n").length;
}
