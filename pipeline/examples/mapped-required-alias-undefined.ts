// `Required` over an optional field whose type names an alias holding
// `undefined`, without `exactOptionalPropertyTypes`: TypeScript takes
// `undefined` from what the alias denotes, through a chain of aliases too,
// so the field is a `string`; an alias of a record, directly or through
// another alias, holds no `undefined` and is kept.
type Missing = undefined;
type Again = Missing;
type Maybe<T> = T | Missing;
interface Point {
  x: number;
}
type Spot = Point;
export function make(): Required<{ b?: string | Missing }> {
  return { b: "b" };
}

export function read(x: Required<{ b?: Maybe<string>; p?: Point | undefined }>): number {
  return x.b.length + x.p.x;
}

export function chained(x: Required<{ b?: string | Again; s?: Spot | undefined }>): number {
  return x.b.length + x.s.x;
}
