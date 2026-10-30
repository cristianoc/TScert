// An indexed access at an optional method a module of the project adds to
// the standard library's `Boolean`: a standard library interface is read
// through its overlay, and the access is refused.
export function probe(d: Boolean): Boolean["probe"] {
  return d.probe;
}
