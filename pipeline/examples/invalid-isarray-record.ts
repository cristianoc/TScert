// An open record may be an array carrying its keys, so `Array.isArray`
// does not remove it from the arm where the test holds: `x` there may be a
// `Foo` that is an array of unknown elements, `readonly unknown[]`, not a
// `number[]`, though TypeScript narrows it to `number[]`.
type Foo = { a: string; b: number };

function elements(x: number[] | Foo): number[] {
  if (Array.isArray(x)) return x;
  return [];
}
