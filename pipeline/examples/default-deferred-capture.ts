// Safe JavaScript: this closure reads the same parameter binding after its
// initializer runs, rather than capturing the raw undefined argument value.
function deferredDefaultCapture(seed: boolean): boolean {
  const pick = (
    read: () => boolean = (): boolean => later,
    later: boolean = seed,
  ): boolean => read();
  return pick();
}

// Two pending closures form an acyclic dependency chain. Effectful defaults
// keep source order, and the closure reads the cell at invocation time.
function deferredChain(seed: boolean): boolean {
  const cell: { value: boolean } = { value: seed };
  const pick = (
    first: () => boolean = (): boolean => second(),
    second: () => boolean = (): boolean => later,
    before: boolean = (cell.value = false),
    later: boolean = cell.value,
    after: boolean = (cell.value = seed),
  ): boolean => first();
  return pick();
}
