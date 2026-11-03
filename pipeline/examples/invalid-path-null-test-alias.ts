// A write through an alias between a test of a path of two members and the
// path's read: the write ends the read link of the path's last member, so
// the read is of its declared type. TypeScript keeps the narrowing. Under
// Node the alias is the tested object and `null` is returned where a string
// is.
type Slots = { observation: string; result: string | null };

export function result(
  binder: { readonly resolution: Slots },
  alias: Slots,
): string {
  if (binder.resolution.result === null) return "";
  alias.result = null;
  return binder.resolution.result;
}
