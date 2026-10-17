// A declared class whose heritage is a call: in a declared module no code
// the client runs makes the call, so nothing checks what it applies, and the
// heritage is refused.
import type { Made } from "@fixture/lib";
export function f(x: Made): number {
  return x.n;
}
