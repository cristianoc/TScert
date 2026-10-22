// The form of `type-term.mts#visitType`: a parameter declared a
// `ReadonlySet<string>` whose default is a fresh `Set<string>`. After the
// default the binding holds either, and the spread binds the `next` of
// whichever iterator GetIterator gives. The flow after the default does not
// establish the binding's claim at the next point (a read of `size` alone
// fails the same way), which no change of the bind reaches.
export function merged(
  more: readonly string[],
  bound: ReadonlySet<string> = new Set(),
): number {
  return new Set([...bound, ...more]).size;
}
