// The initializer closure retains the original cell; the body writes its copy.
// Node returns 0, even though the body assigns 1 before calling get.
export function probe(): number {
  for (let i: number = 0, get: () => number = () => i; i < 1; i = i + 1) {
    i = 1;
    return get();
  }
  return -1;
}
