// TypeScript lets a readonly dictionary pass as a mutable one, though its
// locations may hold narrower contracts than a writer would store at.
function unfreeze(x: { readonly [key: string]: boolean }): {
  [key: string]: boolean;
} {
  return x;
}
