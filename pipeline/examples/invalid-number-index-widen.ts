// TypeScript lets a mutable number index widen its contract, though a writer
// through the wider one could store a string where a holder of the narrower
// one reads a number. A writable index is invariant, over any keys.
function widen(x: { [k: number]: number }): { [k: number]: number | string } {
  return x;
}
