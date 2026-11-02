// A nullable alias retains permission to append null after a content test.
function settled(values: (string | null)[]): values is string[] {
  return values.every((value) => value !== null);
}
export function unsafe(original: (string | null)[]): string {
  const narrowed = original;
  if (!settled(narrowed)) return "";
  original.push(null);
  return narrowed[narrowed.length - 1].toUpperCase();
}
