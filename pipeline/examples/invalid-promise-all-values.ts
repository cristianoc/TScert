// `Promise.all` is read at an array of promises: plain values, which
// JavaScript adopts one by one, are not admitted, and a thenable among them
// would settle to what its `then` passes on.
function gathered(xs: { n: number }[]): Promise<{ n: number }[]> {
  return Promise.all(xs);
}
