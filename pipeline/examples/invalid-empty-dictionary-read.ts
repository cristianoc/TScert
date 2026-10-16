// An empty literal is a dictionary with no key: TypeScript accepts the read
// under --strict, but it is `undefined`.
function first(): boolean {
  const d: { readonly [key: string]: boolean } = {};
  return d["first"];
}
