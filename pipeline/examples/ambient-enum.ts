// An ambient enum is the environment's object, assumed at its members'
// object type as a `declare const` is: an initialized member at its value, an
// uninitialized one, which TypeScript leaves opaque, at `number`. The object
// type states no reverse mapping, and `Level` is the union of the members'
// values, `number` for an opaque one.
declare enum Level {
  Low = 0,
  High,
}
declare enum Named {
  Red = "red",
  Blue = "blue",
}
export function low(): 0 {
  return Level.Low;
}
export function high(): number {
  return Level.High;
}
export function anyLevel(n: number): Level {
  return n;
}
export function red(): "red" {
  return Named.Red;
}
export function named(x: Named): "red" | "blue" {
  return x;
}
