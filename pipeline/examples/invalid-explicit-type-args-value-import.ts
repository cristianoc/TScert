// `new` constructs the instance its explicit type arguments name. A
// `Holder<1>`'s value field is mutable: TypeScript lets it pass as a
// `Holder<number>`, through which a `2` could be stored.
import { Holder } from "@fixture/lib";
export function widen(): Holder<number> {
  const h = new Holder<1>(1);
  return h;
}
