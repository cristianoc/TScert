// An import binding no name runs the module for its effects alone, which no
// binding of the file reads: refused.
import "@fixture/lib";

export function one(): number {
  return 1;
}
