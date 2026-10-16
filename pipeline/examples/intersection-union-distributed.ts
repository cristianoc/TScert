// An intersection with a union operand is the union of the intersections
// with each arm, `(A | B) & C` as `(A & C) | (B & C)`: a read of what `C`
// states splits on the arms, an array's among them.
type Named = { name: string; value: number };

export function extra(
  x: (Array<number> | Named) & { extra: boolean },
): boolean {
  return x.extra;
}

export function flag(
  x: (readonly string[] | { name: string }) & { flag: number },
): number {
  return x.flag;
}
