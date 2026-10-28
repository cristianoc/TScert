// An inherited custom getter at an audited key executes on every read.
class Base {
  reads: number = 0;
  get kind(): number {
    this.reads = this.reads + 1;
    return this.reads;
  }
}
class Derived extends Base {}
function read(x: unknown): unknown {
  return typeof x === "object" && x !== null && "kind" in x
    ? x.kind
    : undefined;
}
export function counted(): unknown {
  const value = new Derived();
  read(value);
  return read(value);
}
