// Construct signatures of standard library globals, through the reviewed
// overlay: `new Array<T>()` and `new Array()` are a fresh empty array, at
// the element type written or expected; `new Error(m)` with a string owns
// `message`, that string.
function numbers(): number[] {
  const xs = new Array<number>();
  xs.push(1);
  return xs;
}

function strings(): Array<string> {
  const r: Array<string> = new Array();
  return r;
}

function message(): string {
  const e = new Error("boom");
  return e.message;
}
