// An interface extending another whose method takes a narrower parameter,
// which TypeScript admits by comparing methods bivariantly: a closure over
// the base calls the method with a string, and the extending object's
// method, which takes a number, returns it where a number is promised. The
// element is not within the closure's parameter: its method is not within
// the base's.
interface Base {
  step(by: number | string): number;
}
interface Counter extends Base {
  step(by: number): number;
}

export function wrong(xs: Counter[]): number[] {
  const once = (b: Base): number => b.step("1");
  return xs.map(once);
}
