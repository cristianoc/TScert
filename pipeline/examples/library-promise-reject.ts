// `Promise.reject(r)` is a promise rejected with `r`: awaiting it throws,
// an outcome, so it settles to no value and is a promise of every type
// (`%PromiseReject%`). The reason is any value.
function failed(): Promise<never> {
  return Promise.reject("boom");
}

async function awaited(): Promise<number> {
  const p: Promise<number> = Promise.reject(new Error("x"));
  const n: number = await p;
  return n + 1;
}
