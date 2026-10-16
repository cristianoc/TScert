// A regex's `lastIndex` is not enumerable: a copy lacks it. The model's regex
// states no `lastIndex`, so it meets no view stating one, and the call is
// refused.
function copy(x: { lastIndex: number }): number {
  return { ...x }.lastIndex;
}

export function viewed(): number {
  return copy(/a/);
}
