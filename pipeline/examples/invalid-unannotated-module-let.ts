// A module `let` the module's functions read is a unit boundary: its type
// is written. Unannotated, it is refused.
let count = 0;

export function bump(): number {
  count = count + 1;
  return count;
}
