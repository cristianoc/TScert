// A callback's stated effect, read through a copy of the verifier's
// declarations: `m.pattern` keeps the element's spine growth within its
// statement, so `map` over a dense array returns a dense array.
type Span = [number, number];
type PatternAst =
  | { k: "name"; name: string; pos: Span }
  | { k: "array"; pos: Span; elems: PatternElemAst[] };
interface PatternElemAst { index: number; target: PatternAst; }
type PM = {
  pattern: (p: PatternAst, ...further: unknown[]) => Modifies<{ values: "any"; spines: "grow" }, PatternAst>;
};
export function mapPat(p: PatternAst, m: PM): Modifies<{ values: "any"; spines: "grow" }, PatternAst> {
  switch (p.k) {
    case "name": return p;
    case "array": return { ...p, elems: p.elems.map(q => ({ ...q, target: m.pattern(q.target) })) };
  }
}
