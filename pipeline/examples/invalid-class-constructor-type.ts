// A class taking a Boolean does not accept a number: it is not a
// `new (on: number) => Flag`.
class Flag {
  on: boolean;
  constructor(on: boolean) {
    this.on = on;
  }
}
function build(c: new (on: number) => Flag): Flag {
  return new c(1);
}
export function go(): Flag {
  return build(Flag);
}
