// A Promise is not the number it will settle to.
export function wrong(p: Promise<number>): number {
  return p;
}
