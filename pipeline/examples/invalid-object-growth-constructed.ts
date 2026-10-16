// A `new` of a constructor value from elsewhere may keep the instance it
// returns: the write that would add the key is refused.
export function viaParameter(make: new () => { x?: number }): void {
  const b = new make();
  b.x = 1;
}
