// A `message` listener is called with values another process sends: an
// overload no reviewed entry lists, refused.
export function listen(onMessage: (message: unknown) => void): void {
  process.on("message", onMessage);
}
