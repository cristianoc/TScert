type Arms = (string & { a: number }) | { b: number };
export function union(x: Arms): { b: number } {
  return { ...x };
}
export function direct(x: (string & { a: number }) | { b: number }): {
  b: number;
} {
  return { ...x };
}
export function product(x: Arms & { c: string }): { b: number; c: string } {
  return { ...x };
}
