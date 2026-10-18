// Two modules importing from each other: the qualified-dependency graph
// takes one direction of the cycle, `ping` reading `pong` qualified.
import { pong } from "@fixture/pong";
export function ping(n: number): number {
  return n > 0 ? pong(n - 1) : 0;
}
