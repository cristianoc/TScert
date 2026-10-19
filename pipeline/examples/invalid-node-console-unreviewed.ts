// `console`, declared by the DOM's library and by `@types/node`: a member no
// reviewed entry lists is refused, whichever declares it.
export function warn(): void {
  console.warn("careful");
}
