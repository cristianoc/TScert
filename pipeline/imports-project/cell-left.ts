// A cycle of modules with cells: `left`'s initialization calls `right`'s
// function, which reads `right`'s cell. Where `right` is evaluated first
// (an importer of `right` reaches `left` through it), `left` runs before
// `right`'s cell is initialized and the read throws.
import { readRight } from "@fixture/cell-right";
let left: number = readRight();
export function readLeft(): number {
  return left;
}
