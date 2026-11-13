// A module binding and a captured binding: each is a cell its binding
// allocates, typed by the binding's storage capability (role `cell`),
// beside an object literal's property (role `field`).
let total: number = 0;

export function add(x: number): number {
  total = total + x;
  return total;
}

export function counter(): () => number {
  let n: number = 0;
  const next = (): number => {
    n = n + 1;
    return n;
  };
  return next;
}

export function box(x: number): { value: number } {
  const b = { value: x };
  b.value = b.value + 1;
  return b;
}
