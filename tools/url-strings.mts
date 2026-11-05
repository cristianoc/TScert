/* Part of the trusted front end: the front end's two operations on WHATWG
 * URLs, each from strings to a string, with the URL it makes kept inside the
 * function. A URL the program held could be handed to other code, which may
 * give it or its search parameters an own member that a later read of its
 * `href` runs (SOURCE-CONTRACTS.md, "Node's `URL`"), so the program holds
 * none: this module is a host boundary, whose callers rely on its signatures
 * and the contract below, audited against Node 26.13.0's
 * `lib/internal/url.js` (SOURCE-REWRITES.md, "URLs as strings").
 *
 * Each function constructs a URL no other code can reach, reads its `href`
 * once, and returns it. Node's URL construction publishes nothing (no
 * diagnostics channel), and the `href` getter of a URL whose search
 * parameters no code has read serializes its parsed record, running no code
 * but Node's under the approved policy that standard objects and prototypes
 * are not tampered with. */
import { pathToFileURL } from "node:url";

/** The `file:` URL of a path, serialized: `pathToFileURL(path).href`. A
 * relative path is resolved against the process's working directory, read
 * through `process.cwd()`. */
export function pathToFileHref(path: string): string {
  return pathToFileURL(path).href;
}

/** `input` parsed against the URL `base`, serialized:
 * `new URL(input, base).href`. Either string that is no URL, or no URL
 * relative to the base, throws a `TypeError`. */
export function resolveHref(input: string, base: string): string {
  return new URL(input, base).href;
}
