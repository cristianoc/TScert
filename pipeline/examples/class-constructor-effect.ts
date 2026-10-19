// Constructors writing their instance's fields, and one also writing a
// module cell: an instance's field writes add keys to the object the
// construction allocates, which changes no earlier location, and the cell
// write changes one.
let made: number = 0;
class Counted {
  n: number;
  constructor(n: number) {
    made = made + 1;
    this.n = n;
  }
}
class Plain {
  n: number;
  constructor(n: number) {
    this.n = n;
  }
}
export function make(): number {
  return new Counted(1).n + new Plain(2).n + made;
}
