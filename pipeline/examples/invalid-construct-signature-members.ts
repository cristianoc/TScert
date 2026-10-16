// A class without the static field a construct type states does not meet it.
class C {
  value: number = 1;
}
type Maker = { new (): C; zero: number };
export function make(K: Maker): number {
  return new K().value + K.zero;
}
export function pass(): number {
  // @ts-expect-error C has no static `zero`
  return make(C);
}
