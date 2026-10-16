// An explicit type argument fixes the instance a plain call is typed at:
// `same<string>` takes a string, which a number is not, although inference
// would have found `number`.
function same<T>(x: T): T {
  return x;
}

export function stated(n: number): string {
  return same<string>(n);
}
