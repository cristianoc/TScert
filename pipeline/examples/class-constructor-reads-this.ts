// A constructor statement that reads `this` could observe the instance
// before its fields are assigned (a method it calls may read one): outside
// the fragment.
class Reads {
  n: number;
  constructor(n: number) {
    this.show();
    this.n = n;
  }
  show(): number {
    return this.n;
  }
}
export function make(): number {
  return new Reads(1).n;
}
