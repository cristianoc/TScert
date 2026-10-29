// A function declaration after a return is hoisted: the live code calls it.
// It is bound before the call.
function hoisted(): number {
  return helper();
  function helper(): number {
    return 1;
  }
}
