// A `switch` whose `case` labels are members of an enum another module
// declares narrows as one on a local enum does (`switch-enum-case-narrowing`):
// reading a member of the imported enum's object writes nothing.
import { Grade } from "@fixture/grades";

type Low = { readonly grade: Grade.Low; readonly low: number };
type High = { readonly grade: Grade.High; readonly high: number };

export function imported(g: Low | High): number {
  switch (g.grade) {
    case Grade.High:
      return g.high;
    case Grade.Low:
      return g.low;
  }
}
