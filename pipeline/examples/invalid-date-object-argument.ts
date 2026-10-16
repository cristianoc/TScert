// `new Date(d)` converts an object argument by its own `valueOf` or
// `toString`, and TypeScript admits any object meeting the `Date`
// interface: the argument is stated at a number or a string.
function copy(d: Date): Date {
  return new Date(d);
}
