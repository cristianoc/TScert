export function copied(
  x: (string & { a: number }) | (number & { b: number }),
): {} {
  return { ...x };
}
