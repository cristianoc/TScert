// A `Set<number>`'s spread holds numbers, not strings.
export function f(s: Set<number>): string[] {
  const a: string[] = [...s] as string[];
  return a;
}
