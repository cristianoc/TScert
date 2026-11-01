// An absent own key can resolve to an inherited function.
export function bound(
  bounds: Readonly<Record<string, string>> | undefined,
  name: string,
): string | null {
  return bounds?.[name] ?? null;
}
