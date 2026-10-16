// An ambient constant holds any value of its declared type, null included.
declare const label: string | null;
export function wrong(): string {
  return label;
}
