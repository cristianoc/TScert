// A class is a value with construct signatures: passed where one is expected,
// it is constructed there with `new`.
class Flag {
  on: boolean;
  constructor(on: boolean) {
    this.on = on;
  }
}
function build(c: new (on: boolean) => Flag): Flag {
  return new c(true);
}
export function go(): boolean {
  return build(Flag).on;
}
