// A certified module holding a module cell: its initialization unit
// allocates and initializes the cell, and its function reads and writes it.
let calls: number = 0;

export function next(): number {
  calls = calls + 1;
  return calls;
}
