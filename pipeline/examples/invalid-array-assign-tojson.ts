// `Object.assign` of a source owning `toJSON` onto an array would give the
// array an own `toJSON`, which arrays own none of: refused.
export function hook(xs: number[]): string {
  Object.assign(xs, { toJSON: (): undefined => undefined });
  return JSON.stringify(xs);
}
