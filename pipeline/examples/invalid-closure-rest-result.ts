// A call with no rest arguments has no first element.
export function bad(): string {
  const first = (...names: string[]) => names[0];
  return first();
}
