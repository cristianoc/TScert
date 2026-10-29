// A conditional inferring a parameter list from a concrete construct
// signature, `new (...args: infer X) => any`: an abstract class's typeof
// does not meet it, so TypeScript takes the false arm, `{ fallback: string }`.
// The reader reads only the `abstract new` form, which every class meets,
// and refuses this one rather than read the class's constructor.
declare abstract class Shape {
  constructor(sides: number);
}
type Params<T> = T extends new (...args: infer X) => any ? X : { fallback: string };
export function label(): string {
  const chosen: Params<typeof Shape> = { fallback: "none" };
  return chosen.fallback;
}
