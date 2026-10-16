// `then` is a host-relative member with quantified signatures: the call binds
// it to its promise and names its instance, `TResult1 := string` through
// `TResult1 | PromiseLike<TResult1>`, below the member's scheme.
export function show(p: Promise<number>): Promise<string> {
  return p.then((n: number) => n.toString());
}
