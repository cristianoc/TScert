// `Object.assign(arrow, literal)` without type arguments: the function
// carrying the literal's fields, at the arrow's type and the literal's record
// TypeScript infers, called and read.
type Counter = { (step: number): number; label: string };

export function counter(): Counter {
  return Object.assign((step: number) => step + 1, { label: "count" });
}

export function scaled(): number {
  const twice = Object.assign((n: number) => n * 2, { scale: 2 });
  twice.scale = 3;
  return twice(3) + twice.scale;
}
