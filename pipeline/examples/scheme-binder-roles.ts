// A declaration passed through, whose method `test.mts` replaces in the
// parser's document by generic methods the parser does not write: one whose
// argument pack `P` sits beside a nested generic method binding its own `P`,
// and one whose nested method uses the outer `P` as a value.
interface Runner {
  run(x: number): number;
}

export function pass(r: Runner): Runner {
  return r;
}
