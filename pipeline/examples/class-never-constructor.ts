// A construct signature is contravariant in its parameters: a class taking a
// Boolean is a `new (p: never) => Flag`, the pattern of the runtime's
// `ResourceClass<C, never>`.
class Flag {
  on: boolean;
  constructor(on: boolean) {
    this.on = on;
  }
}
function keep(c: new (p: never) => Flag): null {
  return null;
}
export function go(): null {
  return keep(Flag);
}
