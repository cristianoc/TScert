// Node's `setTimeout` schedules a callback the host calls with no argument
// between synchronous jobs, and returns a timer, which `clearTimeout`
// cancels.
export function later(done: () => void, ms: number): void {
  const timer = setTimeout(() => done(), ms);
  clearTimeout(timer);
}
export function soon(done: () => void): void {
  setTimeout(done);
}
