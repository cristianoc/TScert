// An import of a module in an import cycle: the pipeline certifies `ping`
// with `pong` read qualified and `pong`'s read of `ping` at its ordinary
// signature, so the qualified reads form no cycle.
import { ping } from "@fixture/ping";
export function parity(n: number): number {
  return ping(n);
}
