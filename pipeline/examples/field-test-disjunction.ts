// A disjunction of field tests keeps, where it holds, the object's arms whose
// field passes either test, and, where it fails, the arms whose field passes
// neither: on one object, on two objects, and over three arms.
type Shape =
  | { kind: 1; x: number }
  | { kind: 2; x: string }
  | { kind: 3; y: number };

export function either(n: Shape): number | string {
  if (n.kind === 1 || n.kind === 2) return n.x;
  return n.y;
}

export function neither(n: Shape): number {
  if (n.kind !== 3 && n.kind !== 1) return 0;
  return n.kind === 3 ? n.y : n.x;
}

export function both(a: Shape, b: Shape): number {
  if (a.kind === 3 || b.kind === 3) return 0;
  const p = a.x;
  const q = b.x;
  return (typeof p === "number" ? p : 1) + (typeof q === "number" ? q : 1);
}

export function three(n: Shape): number {
  if (n.kind === 1 || n.kind === 2 || n.kind === 3) return 1;
  const never: never = n;
  return never;
}

export function mixed(n: Shape, b: Shape): number {
  if (n.kind === 1 || b.kind === 2) return n.kind;
  return 0;
}

export function negated(n: Shape): number {
  if (!(n.kind === 1 || n.kind === 2)) return n.y;
  return 0;
}
