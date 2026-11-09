// A handler receives the slot at the throwing node (SOURCE-ELABORATION.md,
// "Slot or cell"): `acc = fresh` rebinds the slot before `fail()` throws,
// and no node before the write may throw, so the handler's `acc` holds the
// array the body allocated, a fresh value, and its `pop` changes no store
// the frame names; `xs`, which `acc` held before, keeps its elements (run
// under Node: `reset({ open: [] }, ["a"])` is 1).
type Runs = { /** @stable */ readonly open: number[] };

function fail(): number {
  throw new Error("fail");
}

function use(a: string[], n: number): number {
  return a.length + n;
}

export function reset(runs: Runs, xs: string[]): Modifies<{ values: "any"; "runs.open[*]": "any" }, number> {
  let acc: string[] = xs;
  const fresh: string[] = [];
  try {
    use((acc = fresh), fail());
  } catch {
    acc.pop();
    runs.open.push(0);
    return xs.length;
  }
  return 0;
}

// The handler reads the slot the write rebound before the throw (run under
// Node: `caught()` is 0).
export function caught(): number {
  let acc: string[] | null = null;
  const fresh: string[] = [];
  try {
    use((acc = fresh), fail());
  } catch {
    return acc === null ? -1 : acc.length;
  }
  return -2;
}
