// A closure parameter its block body assigns is a cell holding its argument,
// at its annotation, as a function's is: a write of a number leaves it
// holding one.
export function make(): (p: string | number) => number {
  return (p: string | number): number => {
    p = 5;
    const z: number = p;
    return z;
  };
}
