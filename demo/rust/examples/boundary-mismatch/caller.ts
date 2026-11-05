import { scale } from "./lib.js";

// TypeScript accepts this caller, and TScert verifies it against lib.d.ts;
// but lib.d.ts declares `scale` over numbers, and lib.rs takes i64s.
export function doubled(x: number): number {
  return scale(x, 2);
}
