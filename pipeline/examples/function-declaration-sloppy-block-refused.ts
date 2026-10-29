// A file with no import or export may run as a script, sloppy code, where
// Annex B also assigns a block's function declaration to a binding of the
// enclosing function when the declaration is evaluated: refused at it.
function outer(flag: boolean): number {
  if (flag) {
    function one(): number {
      return 1;
    }
    return one();
  }
  return 0;
}
