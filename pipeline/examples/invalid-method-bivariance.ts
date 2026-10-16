// Method parameters are contravariant; TypeScript's method bivariance would
// let an animal reach a handler that needs a dog.
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
export function widen(h: DogHandler): AnimalHandler {
  return h;
}
