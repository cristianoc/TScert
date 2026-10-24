// A statement on a method of a generic class: the method quantifies the
// class's binders, so its code is checked at the bounds its claim states.
export class Box<T> {
  value: T;
  constructor(value: T) {
    this.value = value;
  }
  get(): Within<{ value: "keep"; store: "keep" }, T> {
    return this.value;
  }
}
