// A client obligation (`@clients`) on a type of a package whose exports are
// a pattern: the package's interface, which the obligation's row bounds, is
// not known, and the tag is refused where it is written.
/** @clients {} */
export type Handle = { readonly size: number };

export function size(h: Handle): number {
  return h.size;
}
