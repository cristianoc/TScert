// A readonly view cannot supply the write capability required by a callback.
function readonlyArgument(
  write: (target: { value: number }) => number,
  input: { readonly value: number },
): number {
  return write(input);
}
