// A mapper producing plain JSON arrays. EagerCollection intersects its values
// with DepSafe (`V & DepSafe`); `map` is instantiated at `V2 := readonly
// number[]`, which is not DepSafe, and its result's values are the meet of the
// array with DepSafe's alternatives, as TypeScript reads them.
import type {
  Context,
  EagerCollection,
  Mapper,
  Values,
} from "@fixture/collections";
class Wrap implements Mapper<string, number, string, readonly number[]> {
  mapEntry(
    key: string,
    values: Values<number>,
    _context: Context,
  ): Iterable<[string, readonly number[]]> {
    return [[key, [values.getUnique()]]];
  }
}
export function wrap(
  c: EagerCollection<string, number>,
): EagerCollection<string, readonly number[]> {
  return c.map(Wrap);
}
