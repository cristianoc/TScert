// `hostname`, which a program module re-exports from `node:os` by
// `export *`: the binding is `node:os`'s own export (run under Node: it
// answers `os.hostname()`), which no entry of the overlay reviews, so it is
// refused where it is imported, as a direct import of it is.
import { hostname } from "@fixture/node-os-star";
export function probe(): string {
  return hostname();
}
