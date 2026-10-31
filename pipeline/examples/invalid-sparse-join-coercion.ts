// An unrestricted callback permits holes; present objects still need safe conversion.
export function wrong(
  xs: string[],
  text: (x: string) => { toString: (x: number) => string },
): string {
  return xs.map((x) => text(x)).join(", ");
}
