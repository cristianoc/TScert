// A handler receives the slot at the throwing node (SOURCE-ELABORATION.md,
// "Slot or cell"), here before the write: `fail()` runs before `acc =
// fresh`, so the handler's `acc` holds the caller's `xs`, and its `pop` is
// refused at the regional check (run under Node: `reset({ open: [] },
// ["a"])` is 0).
type Runs = { /** @stable */ readonly open: number[] };

function fail(): number {
  throw new Error("fail");
}

function use(n: number, a: string[]): number {
  return a.length + n;
}

export function reset(runs: Runs, xs: string[]): Modifies<{ values: "any"; "runs.open[*]": "any" }, number> {
  let acc: string[] = xs;
  const fresh: string[] = [];
  try {
    use(fail(), (acc = fresh));
  } catch {
    acc.pop();
    runs.open.push(0);
    return xs.length;
  }
  return 0;
}
