// A key-adding write on a local's own fresh object, which nothing else has
// reached: the local holds the copy of the object with the key (TypeScript
// refuses the write).
export function grow(): { x: number; y: string } {
  const obj = {};
  obj.x = 5;
  obj.y = "hi";
  return obj;
}

// The added field's contract is the value's declared type, not a fresh
// object's exact keys.
export function nested(): { inner: { value: number } } {
  const inner = {};
  inner.value = 42;
  const outer = {};
  outer.inner = inner;
  return outer;
}

// Once added, the key is an ordinary field: a second write stores into it.
export function reassign(): number {
  const o = {};
  o.x = 1;
  o.x = 2;
  return o.x;
}

// A literal with fields, a literal key, a read before the write.
export function onLiteral(): { a: number; b: boolean; c: string } {
  const o = { a: 1 };
  const before = o.a;
  o.b = before > 0;
  o["c"] = "s";
  return o;
}

// Added on one path only: where the paths join the key is optional, which
// the object's exact keys state.
export function inBranch(c: boolean): { x?: number } {
  const o = {};
  if (c) {
    o.x = 1;
  }
  return o;
}

// A declaration inside the loop body is a fresh object each time round.
export function inLoop(n: number): number {
  let total = 0;
  for (let i = 0; i < n; i++) {
    const o = {};
    o.v = i;
    total = total + o.v;
  }
  return total;
}

// An object a spread built is fresh too.
export function spreadBuilt(p: { a: number }): { a: number; b: string } {
  const o = { ...p };
  o.b = "b";
  return o;
}

// An optional field of the annotation, written: its key added at its type.
export function optionalAnnotated(): { a?: number; b: number } {
  const o: { a?: number; b: number } = { b: 0 };
  o.a = 3;
  return o;
}

// A `let` holding its own copy, and a constant bound to it since: the copy
// with the key is rebound to both, the cell and the constant.
export function inCellWithAlias(src: { [k: string]: number }): number {
  let o = { ...src };
  const ref = o;
  o.x = 5;
  return (ref.x ?? 0) + o.x;
}

// A `new` of a class the file declares: its constructor reads no `this` and
// ends in the instance's allocation, which nothing else has reached.
class WithOptional {
  x: number = 0;
  constructor(public y?: string) {}
}
export function onInstance(): string | undefined {
  const b = new WithOptional("s");
  b.y = undefined;
  return b.y;
}

// A write through an annotated constant bound to the object: every holder
// holds the copy with the key, at which a view stating the key reads it.
export function throughAnnotatedAlias(): number {
  const o = { y: 0 };
  const w: { x?: number; y: number } = o;
  w.x = 1;
  const view: { x?: number } = o;
  return (view.x ?? 0) + (w.x ?? 0);
}
