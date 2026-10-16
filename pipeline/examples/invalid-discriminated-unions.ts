// A call may write the field between the test and the read: what it held at
// the test is no longer known.
function reset(o: { val: string | null }): void {
  o.val = null;
}

function stale(o: { val: string | null }): string {
  if (o.val !== null) {
    reset(o);
    return o.val;
  }
  return "";
}
