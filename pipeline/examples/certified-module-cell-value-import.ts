// An imported function of a certified module that writes a module cell of
// its own: the module's run checks its initialization, which allocates the
// cell, and the function's unit at the cell's contract.
import { next } from "@fixture/counter";

export function twice(): number {
  return next() + next();
}
