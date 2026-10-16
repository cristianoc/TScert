// The clauses of a switch share one scope: `m`, declared in case 1, is the
// binding `default` reads, initialized there when case 1 falls through and
// read by the closure only then. Each clause's statements are lowered in a
// scope of their own, so the gate refuses a name read outside the clause
// declaring it.
export function fall(x: number): number {
  switch (x) {
    case 1:
      let m = 1;
    default:
      const r = (): number => m;
      return x === 1 ? r() : 0;
  }
}
