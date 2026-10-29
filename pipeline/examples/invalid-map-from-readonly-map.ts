// `new Map` of a `ReadonlyMap`: any object with the readers meets it, its
// iterator among them, which `new Map` runs, and whose entries' `0` and `1`
// it reads; only a host `Map`'s reading view is stated, whose iterator is
// the host's and yields fresh entry arrays.
export function copy(names: ReadonlyMap<string, number>): Map<string, number> {
  return new Map(names);
}
