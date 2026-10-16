// No tuple of the union has a string position.
interface Stepper {
  step(...[by]: [] | [number]): string;
}
export function wrong(s: Stepper): string {
  return s.step("two");
}
