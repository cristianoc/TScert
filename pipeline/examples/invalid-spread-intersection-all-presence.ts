export function copied(
  x: { k: string | number } & { k: string | boolean } & { k?: string },
): { k: string } {
  return { ...x };
}
