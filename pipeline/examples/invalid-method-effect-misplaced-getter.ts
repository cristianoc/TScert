// `Within` on a getter: an accessor is outside the fragment, and a
// statement on one with it.
export class Box {
  value: number = 0;
  get doubled(): Within<{ value: "keep"; store: "keep" }, number> {
    return this.value * 2;
  }
}
