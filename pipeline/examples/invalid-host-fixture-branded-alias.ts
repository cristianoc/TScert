// An alias of the branded string is the branded string: a client result at
// it is refused (reading rule 5).
import type { Path } from "@fixture/host";

type Location = Path;
export function forged(l: Location): Location {
  return l;
}
