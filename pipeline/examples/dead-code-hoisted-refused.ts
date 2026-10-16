// A function declaration after a return is hoisted: the live code calls it.
// Dropping it would change what `helper` names, so the gate refuses.
function hoisted(): number {
  return helper();
  function helper(): number {
    return 1;
  }
}
