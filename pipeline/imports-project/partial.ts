// A module whose function `jumped` the gate refuses (a function declaration
// after its `return`). `relayed` calls it, `chained` calls `relayed`,
// `passed` passes it as a value, `inClosure` calls it in a closure and
// `defaulted` in a parameter default: each reads it. `shadowed` reads its
// own parameter of the same name, and `kept` reads no function.
function jumped(x: number): number {
  return inner(x);
  function inner(y: number): number {
    return y;
  }
}
export function relayed(x: number): number {
  return jumped(x);
}
export function chained(x: number): number {
  return relayed(x);
}
export function passed(xs: number[]): number[] {
  return xs.map(jumped);
}
export function inClosure(xs: number[]): number[] {
  return xs.map((x) => jumped(x));
}
export function defaulted(x: number, y: number = jumped(x)): number {
  return y;
}
export function shadowed(jumped: number): number {
  return jumped + 1;
}
export function kept(x: number): number {
  return x + 1;
}
