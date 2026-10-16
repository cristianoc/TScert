// Falling off the end of a closure returns undefined, which a `number`
// result does not admit.
function partial(flag: boolean): number {
  const f = (): number => {
    if (flag) {
      return 1;
    }
  };
  return f();
}
