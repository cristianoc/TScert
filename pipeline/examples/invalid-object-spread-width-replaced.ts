// A spread after a named field may replace it: `extra`, held at
// `{ id: number }`, is an object that also holds `name: 1`, so the copy's
// `name` is no string, though TypeScript admits the copy at the expected
// `{ name: string }` (under Node `wrong()` returns `{ name: 1, id: 1 }`).
function make(): { id: number; name: number } {
  return { id: 1, name: 1 };
}

export function wrong(): { name: string } {
  const extra: { id: number } = make();
  return { name: "x", ...extra };
}
