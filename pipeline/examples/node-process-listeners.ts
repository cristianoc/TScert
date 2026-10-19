// Node's `process.on` and `process.once` at named events: `exit` and
// `beforeExit` call the listener with the exit code, a signal with its
// name. A listener written here may ignore its argument, and the
// registration is chained. `kill` sends a signal: `true`, a throw, or the
// process ending.

export function register(
  onExit: (code: number) => void,
  onSignal: (signal: string) => void,
): void {
  process.on("exit", onExit);
  process.once("beforeExit", (code: number) => {
    onExit(code);
  });
  process.on("exit", () => {});
  process.on("SIGHUP", onSignal).on("SIGUSR2", onSignal);
}
// `beforeExit` is emitted again whenever its listeners scheduled more work.
export function whenIdle(listener: (code: number) => void): void {
  process.on("beforeExit", listener);
}
export function stop(): true {
  return process.kill(process.pid, "SIGTERM");
}
