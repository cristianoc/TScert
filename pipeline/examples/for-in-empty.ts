// Enumeration needs its internal array contract even with no source array type.
export function emptyKeys(): void {
  const empty = {};
  for (const key in empty) {
    const name: string = key;
  }
}
