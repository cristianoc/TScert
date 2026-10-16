// `Promise.resolve` and `Promise.all` through the reviewed overlay, as the
// intrinsics that state the same steps: `Promise.resolve(v)` of a primitive
// is a promise settled to it, as an async function's return is;
// `Promise.resolve()` settles to `undefined`; `Promise.all` of promises is a
// promise of the array of their values.
function resolved(): Promise<number> {
  return Promise.resolve(42);
}

function settled(): Promise<void> {
  return Promise.resolve();
}

function gathered(ps: Array<Promise<number>>): Promise<Array<number>> {
  return Promise.all(ps);
}

async function awaited(ps: Array<Promise<string>>): Promise<number> {
  const xs = await Promise.all(ps);
  const n = await Promise.resolve(1);
  return n + xs.length;
}
