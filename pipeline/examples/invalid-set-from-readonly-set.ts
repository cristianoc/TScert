// `new Set` of a `ReadonlySet`: any object with the readers meets it, its
// iterator among them, which `new Set` runs; only a host `Set`'s reading
// view is stated, whose iterator is the host's.
export function copy(names: ReadonlySet<string>): Set<string> {
  return new Set(names);
}
