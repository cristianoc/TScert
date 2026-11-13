// An importer reading a postcondition its module's check refuses: `breaksOf`
// returns `source.length` elements where its `@ensures` states one more, so
// no interface entry states the postcondition and the import is read at the
// ordinary effect; the read `breaks[source.length]!` is refused. Under Node
// `last("ab")` returns `undefined`, not a number.
import { breaksOf } from "@fixture/false-ensures";

export function last(source: string): number {
  const breaks = breaksOf(source);
  return breaks[source.length]!;
}
