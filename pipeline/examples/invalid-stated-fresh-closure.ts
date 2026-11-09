// A closure returning a captured array, passed where a function type states
// a fresh result: the array is no array the call allocated, so no rule
// introduces the closure at the type. A caller relying on the promise would
// read two calls' results as two arrays (`invalid-stated-fresh-input`
// shows the consequence under Node).
export function once(make: () => Fresh<number[]>): number {
  return make().length;
}

export function use(xs: number[]): number {
  return once(() => xs);
}
