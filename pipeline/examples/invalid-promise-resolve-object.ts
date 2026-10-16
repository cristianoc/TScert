// `Promise.resolve` adopts a thenable instead of settling to it, and a
// record may own a `then`: `{ then(f) { f("s") } }` meets `{ n: number }`
// and settles to "s". Only a primitive is admitted, as for an async return.
function wrapped(o: { n: number }): Promise<{ n: number }> {
  return Promise.resolve(o);
}
