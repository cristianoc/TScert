export function negated(x: string | number): number {
  if (!(typeof x === "string" && ((x = 0), true))) return 1;
  return x;
}

export function forwarded(x: string | number): number {
  if (!(0, typeof x === "string" && ((x = 0), true))) return 1;
  return x;
}
