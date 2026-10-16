// A rest parameter over a union of tuples, `...[by]: [] | [number]`, is one
// signature per tuple: the method is called with nothing or with a number.
interface Stepper {
  step(...[by]: [] | [number]): string;
}
export function twice(s: Stepper): string {
  s.step();
  return s.step(2);
}
