// Optional chains nested, shadowed, in a closure and skipping effects: every
// chain saves its receiver under one name, and what one chain's test learns
// is not read as another's.
interface Leaf {
  value?: number;
}
interface Inner {
  leaf?: Leaf;
  list?: number[];
}
interface Outer {
  inner?: Inner;
}
// Three links over an element read, returned and tested.
export function deep(os: Outer[]): number {
  if (os[0]?.inner?.leaf?.value) return os[0]?.inner?.leaf?.value ?? -1;
  return 0;
}
// The receiver's name shadowed in a block, a chain on each binding.
export function shadowed(o: Outer | undefined, os: Outer[]): number {
  const before = o?.inner?.leaf?.value ?? 0;
  {
    const o = os[0];
    if (o?.inner?.leaf?.value) return before * 100 + (o?.inner?.leaf?.value ?? 0);
  }
  return before;
}
// A chain inside a closure, over the closure's parameter.
export function values(os: Outer[]): number[] {
  return os.map((o): number => o.inner?.leaf?.value ?? -1);
}
// A skipped link does not run its key: the counter counts the keys run.
export function keysRun(o: Outer | undefined): number {
  const counter = { calls: 0 };
  const v = o?.inner?.list?.[(counter.calls = counter.calls + 1, 0)];
  return counter.calls * 10 + (v ?? 5);
}
