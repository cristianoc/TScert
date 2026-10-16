// `d` is a Dog where the closure is written, as its context says; the closure
// is a Dog handler, which TypeScript's method bivariance then lets stand for
// an Animal handler, and an Animal has no `barks` to read.
interface Animal {
  readonly name: string;
}
interface Dog {
  readonly name: string;
  readonly barks: number;
}
interface DogHandler {
  handle(x: Dog): number;
}
interface AnimalHandler {
  handle(x: Animal): number;
}
const dogs: DogHandler = { handle: (d) => d.barks };
export const animals: AnimalHandler = dogs;
