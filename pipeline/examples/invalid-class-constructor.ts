// A constructed instance's field has its declared type, not another.
class Holder {
  readonly value: boolean;
  constructor(value: boolean) {
    this.value = value;
  }
}
export function wrong(): null {
  return new Holder(true).value;
}
