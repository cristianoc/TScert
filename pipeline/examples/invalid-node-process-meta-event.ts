// `newListener` is emitted while a listener is registered, inside the
// registering call: a meta-event no reviewed entry admits, refused.
export function watch(seen: (event: string | symbol) => void): void {
  process.on("newListener", seen);
}
