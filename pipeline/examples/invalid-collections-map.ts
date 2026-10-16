// A mapper producing strings: EagerCollection.map at its instance returns a
// collection of strings, not the collection of numbers claimed.
import type {
  Context,
  EagerCollection,
  Mapper,
  Values,
} from "@fixture/collections";
class Show implements Mapper<string, number, string, string> {
  mapEntry(
    key: string,
    _values: Values<number>,
    _context: Context,
  ): Iterable<[string, string]> {
    return [[key, key]];
  }
}
export function show(
  c: EagerCollection<string, number>,
): EagerCollection<string, number> {
  // @ts-expect-error: the result is an EagerCollection<string, string>
  return c.map(Show);
}
