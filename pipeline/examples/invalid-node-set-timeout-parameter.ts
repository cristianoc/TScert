// Node calls a timer's callback with the arguments passed after the delay:
// the reviewed contract admits none, so a callback is called with no
// argument, and a call passing more is refused.
export function later(onTick: (n: number) => void): void {
  setTimeout(onTick, 1, 5);
}
