type Box = { v: string };

// The block's `Box` names its block only: after the block, `Box` is the
// module's again, so `outer` and the result hold a number where the
// contract states a string. Read with the block's `Box` past its block, the
// code would meet it.
function leak(n: number): Box {
  {
    type Box = { v: number };
    const inner: Box = { v: n };
    n = inner.v;
  }
  // @ts-expect-error -- `Box` is the module's here
  const outer: Box = { v: n };
  return outer;
}
