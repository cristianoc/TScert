// `Promise<number | string>` is no `Promise<number>`: the target's `then`
// would hand its callback a `string` the source's promises it only as
// `number | string`.
export function narrow(p: Promise<number | string>): Promise<number> {
  // @ts-expect-error Type of returned value is not assignable
  return p;
}
