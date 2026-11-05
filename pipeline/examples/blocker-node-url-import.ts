// `fileURLToPath` from `node:url` and the boundary tools/url-strings.mts, as
// files.mts and family-activation.mts use them: the program holds no URL,
// only serialized URLs, and a URL the resolver answers is tested as a
// string. Node's declarations of `node:url`, which reach `URLSearchParams`
// and `BuiltinIteratorReturn`, are not read.
// Census functions:
// family-activation.mts#activeGuards, family-activation.mts#loadedGuards,
// family-activation.mts#selectionGuard and 9 others of family-activation.mts,
// files.mts#nodeResolve, files.mts#loadModule, files.mts#observeResolution,
// files.mts#resolveObserved, unchecked.mts#check, unchecked.mts#findIn,
// unchecked.mts#decodeResult.
import { fileURLToPath } from "node:url";
import { pathToFileHref, resolveHref } from "../../tools/url-strings.mts";

export function pathOf(url: string): string {
  return fileURLToPath(url);
}

export function hrefOf(path: string): string {
  return pathToFileHref(path);
}

// A specifier resolved against a parent file, as Node resolves a relative
// one: an invalid URL throws.
export function target(specifier: string, parent: string): string | null {
  try {
    return fileURLToPath(resolveHref(specifier, pathToFileHref(parent)));
  } catch {
    return null;
  }
}

// Whether a serialized URL's query and fragment are empty or absent.
export function emptyQueryAndFragment(href: string): boolean {
  const fragment = href.indexOf("#");
  const beforeFragment = fragment < 0 ? href : href.slice(0, fragment);
  const query = beforeFragment.indexOf("?");
  return (
    (fragment < 0 || fragment === href.length - 1) &&
    (query < 0 || query === beforeFragment.length - 1)
  );
}

// A URL the resolver serialized names a file where it starts with `file:`;
// it is kept where its query and fragment are empty.
export function fileOf(url: string | null): string | null {
  const file = url !== null && url.startsWith("file:") ? url : null;
  return file !== null && emptyQueryAndFragment(file)
    ? fileURLToPath(file)
    : null;
}
