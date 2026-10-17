// `lib.limited()` passes the namespace object as `this`, which `limited`'s
// declared `this` parameter constrains; the named import's call would pass
// `undefined`. The call is refused.
import * as lib from "@fixture/lib";

export function limited(): number {
  return lib.limited();
}
