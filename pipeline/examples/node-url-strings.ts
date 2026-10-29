// URLs constructed from strings, held as opaque values at the declared
// `URL`: the program reads no member of them.
import { fileURLToPath, pathToFileURL } from "node:url";
export function pathOf(url: string): string {
  return fileURLToPath(url);
}
export function file(path: string): URL {
  return pathToFileURL(path);
}
export function relative(base: string): URL {
  return new URL("x", base);
}
