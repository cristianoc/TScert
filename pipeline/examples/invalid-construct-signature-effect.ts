// A statement on a construct signature: a construction's effect is its
// class's, which the signature does not state.
export class Box {
  v: number = 0;
}
export function make(
  ctor: new () => Within<{ value: "keep"; store: "keep" }, Box>,
): Box {
  return new ctor();
}
