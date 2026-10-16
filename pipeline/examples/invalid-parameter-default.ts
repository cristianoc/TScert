// A default reading an earlier parameter holds that parameter's type,
// `undefined` included.
export function dependent(
  first?: number,
  second: number | undefined = first,
): number {
  return second;
}
