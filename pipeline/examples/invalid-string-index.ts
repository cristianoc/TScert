// Past its end a string's index reads `undefined`, though TypeScript types
// the read as `string`.
function charAt(s: string, i: number): string {
  return s[i];
}
