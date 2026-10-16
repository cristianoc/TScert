export function caughtString(p: Promise<number>): Promise<number | string> {
  return p.catch<string>((reason: unknown): string => "fallback");
}
