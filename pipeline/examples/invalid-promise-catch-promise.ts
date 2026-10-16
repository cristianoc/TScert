// `catch`'s callback returning a promise of the wrong type: through
// `PromiseLike<TResult>` it instantiates `TResult := string`, and
// `Promise<number | string>` is no `Promise<number>`.
export function recover(p: Promise<number>): Promise<number> {
  // @ts-expect-error Type 'Promise<string | number>' is not assignable to type 'Promise<number>'
  return p.catch((reason: unknown) => Promise.resolve("none"));
}
