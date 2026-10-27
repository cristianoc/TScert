// A getter for `subarray` on `Buffer.prototype` runs at the method's lookup,
// before the call (run under Node: it pops the array): refused.
export function hook(xs: number[]): void {
  Object.defineProperty(Buffer.prototype, "subarray", {
    get() {
      xs.pop();
      return () => Buffer.from("");
    },
  });
}
