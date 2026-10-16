export function forward(
  p: Promise<{ n: number }>,
): Promise<{ n: number } | string> {
  return p.catch<string>((reason: unknown): string => "fallback");
}
