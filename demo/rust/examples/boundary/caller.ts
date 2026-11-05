import { add, greet, scale } from "./lib.js";

export function total(a: number, b: number, c: number): number {
  return add(add(a, b), c);
}

export function doubled(x: bigint): bigint {
  return scale(x, 2n);
}

export function welcome(name: string): string {
  return greet(name) + "!";
}
