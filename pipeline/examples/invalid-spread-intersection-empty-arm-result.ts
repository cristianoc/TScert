export function copied(x: (string & { a: number }) | { b: number }): {
  a: number;
} {
  return { ...x };
}
