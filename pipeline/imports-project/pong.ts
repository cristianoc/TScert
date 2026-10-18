// The other module of the cycle: its read of `ping` closes it, and is read
// at its ordinary signature.
import { ping } from "@fixture/ping";
export function pong(n: number): number {
  return n > 0 ? ping(n - 1) : 1;
}
