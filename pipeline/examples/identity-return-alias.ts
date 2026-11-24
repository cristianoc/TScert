// Pass-based return-alias postconditions (`IndexFact.same`) hold whenever every
// reachable return aliases a parameter — direct return, local alias binding,
// multi-return branches, and chained identity calls — establishing an alias
// link between result and argument at every call site.
/** @invariant this.flags.length === this.widths.length */
type Pair = { flags: Uint8Array; widths: number[] };

function identity(p: Pair): Pair {
  return p;
}

function localAlias(p: Pair): Pair {
  const y = p;
  return y;
}

function multiReturn(p: Pair, flag: boolean): Pair {
  if (flag) return p;
  const y = p;
  return y;
}

function chained(p: Pair): Pair {
  const y = identity(p);
  return y;
}

export function firstViaAlias(p: Pair, flag: boolean): number {
  const a1 = identity(p);
  const a2 = localAlias(a1);
  const a3 = multiReturn(a2, flag);
  const a4 = chained(a3);
  if (a4.flags.length === 0) return 0;
  return p.widths[0]!;
}
