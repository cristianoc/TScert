// A closure parameter assigned a string holds a string: it is no number.
export function make(): (p: string | number) => number {
  return (p: string | number): number => {
    p = "five";
    const z: number = p;
    return z;
  };
}
