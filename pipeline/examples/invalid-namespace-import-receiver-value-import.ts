// `lib.limited()` passes the namespace object as `this`, which `limited`'s
// declared `this` parameter constrains; a call of the binding the member
// reads passes `undefined`. The call is refused where it is written.
import * as lib from "@fixture/lib";

export function limited(): number {
  return lib.limited();
}
