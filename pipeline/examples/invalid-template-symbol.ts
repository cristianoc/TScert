// A symbol in a template: refused, as TypeScript refuses it. Its conversion
// would throw a TypeError.
function show(s: symbol): string {
  return `s=${s}`;
}
