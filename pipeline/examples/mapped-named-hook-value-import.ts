// A hook passed to a declared chain, as `nodeResolve` passes its resolve
// hook to Node's `registerHooks`: the next hook takes `Partial` of the
// context interface the declaration names, read at that interface's fields
// made optional (rule mapped-identity). The hook passes it the context it
// was given with one field replaced, a record with one field, or nothing.
import { resolveThrough } from "@fixture/hooks-ambient";

export function resolveFrom(specifier: string, parent: string): string {
  return resolveThrough(specifier, (requested, context, next) =>
    next(requested, { ...context, parentURL: parent }),
  ).url;
}
export function resolveParent(specifier: string, parent: string): string {
  return resolveThrough(specifier, (requested, _context, next) =>
    next(requested, { parentURL: parent }),
  ).url;
}
export function resolvePlain(specifier: string): string {
  return resolveThrough(specifier, (requested, _context, next) =>
    next(requested),
  ).url;
}
