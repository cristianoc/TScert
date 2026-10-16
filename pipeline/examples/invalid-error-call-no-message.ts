// `Error()` owns no `message`, as `new Error()` does not: the overlay
// states the call at a string message.
function empty(): string {
  const e = Error();
  return e.message;
}
