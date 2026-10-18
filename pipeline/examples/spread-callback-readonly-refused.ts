// A callback's parameter of readonly fields alone admits a host object: a
// spread of it inside the callback is refused (R8, COMPILER-API.md).
function each(
  o: { readonly a: number },
  f: (x: { readonly a: number }) => {},
): {} {
  return f(o);
}
export function launder(o: { readonly a: number }): {} {
  return each(o, (x: { readonly a: number }) => ({ ...x }));
}
