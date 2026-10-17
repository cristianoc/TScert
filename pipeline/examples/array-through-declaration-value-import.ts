// The file writes no array type: the array reaches it through the imported
// value's declaration, and is read at `Array.prototype`'s contract.
import { trio, type Numbers } from "@fixture/lib";

export function count(): number {
  const xs = trio();
  return xs.length;
}

export function doubled(): number {
  return trio().map((x: number): number => x + x).length;
}

export function copied(): Numbers {
  return trio().map((x: number): number => x);
}
