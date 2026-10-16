// Only a closure literal is created at the wider signature. A value typed
// `() => undefined` may be variadic code that reads the actuals its type
// does not mention, so it is not a `(...args: unknown[]) => void`.
function on(listener: (...args: unknown[]) => void): void {
  listener("SIGTERM", 1);
}
export function register(stop: () => undefined): void {
  on(stop);
}
