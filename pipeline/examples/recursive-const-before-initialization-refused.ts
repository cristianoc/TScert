// A constant read in an initializer that is no function literal: the
// initializer runs before the binding holds its value, so the read is refused
// at its location (SOURCE-ELABORATION.md, "Recursive constants").
export function early(): number {
  const f = ((): (() => number) => {
    const g = (): number => f();
    return g;
  })();
  return f();
}
