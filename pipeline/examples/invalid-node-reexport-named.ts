// `hostname`, which a program module re-exports by name from `node:os`:
// the binding is `node:os`'s own export (run under Node: it answers
// `os.hostname()`), which no entry of the overlay reviews, so it is refused
// where it is imported, as a direct import of it is.
import { hostname } from "@fixture/node-os-named";
export function probe(): string {
  return hostname();
}
