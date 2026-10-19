// A destructuring assignment writing `stack` through a parameter typed
// `{ stack: string }`, which an instance of the `Error` family meets: its own
// `stack` stays non-enumerable (run under Node). The receiver's type does not
// exclude an object holding a prototype: refused at the write.
export function traced(o: { stack: string }): string[] {
  [o.stack] = ["s"];
  return Object.keys(o);
}
