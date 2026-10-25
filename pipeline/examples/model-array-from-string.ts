// Array.from of a string needs its string element type on the result.
// Model study: proposal-field-read-on-non-object.ts; study count not supplied.
export function initial(part: string): string {
  return Array.from(part)[0].toUpperCase();
}
