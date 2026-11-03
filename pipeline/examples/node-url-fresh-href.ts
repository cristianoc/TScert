// The `href` of a URL read directly on the expression that makes it, the
// form `url-strings.mts` uses: no other code reaches the URL before the
// read, so `URL.prototype`'s getter serializes it (SOURCE-CONTRACTS.md,
// "Node's `URL`"). Under Node, `resolve("b", "file:///a/")` is
// "file:///a/b" and `fileHref("/x")` is "file:///x".
import { pathToFileURL } from "node:url";
export function resolve(input: string, base: string): string {
  return new URL(input, base).href;
}
export function absolute(input: string): string {
  return new URL(input).href;
}
export function fileHref(path: string): string {
  return pathToFileURL(path).href;
}
