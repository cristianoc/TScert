// A module importing from a module the certified-import examples also
// import: its own reads of `twice` are certified imports, so `quadruple`
// preserves the heap and `doubledAll` passes `twice` to `map`, whose further
// actuals its code discards.
import { twice } from "@fixture/certified";
export function quadruple(x: number): number {
  return twice(twice(x));
}
export function doubledAll(xs: number[]): number[] {
  return xs.map(twice);
}
