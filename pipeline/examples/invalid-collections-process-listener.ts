// A listener taking a number is not a `SignalsListener`, so TypeScript
// resolves the call to `on`'s last overload, whose listener takes `any[]`,
// and accepts it. Node calls it with the signal's name. Read as `unknown[]`,
// that overload admits no listener of a number.
export function register(listener: (code: number) => undefined): void {
  process.on("SIGTERM", listener);
}
