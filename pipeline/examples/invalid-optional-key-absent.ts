// A failed `in` test finds the key absent: the read is `undefined`.
function failedIn(x: { f?: number }): number {
  if (!("f" in x)) {
    return x.f;
  }
  return 0;
}
