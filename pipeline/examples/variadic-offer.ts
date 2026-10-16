// A closure passed where a variadic callback is offered, as `shutdown` is
// passed to `process.on`: it is created at that signature too, since its
// code binds its own parameters, all among the signature's fixed ones, and
// discards every further actual. A `void` result is `unknown` here, so a
// closure returning a promise meets it.
function on(listener: (...args: unknown[]) => void): void {
  listener("SIGTERM", 1);
}
function onEvent(listener: (event: string, ...rest: unknown[]) => void): void {
  listener("SIGINT");
}
export function register(p: Promise<boolean>): void {
  const shutdown = async (): Promise<void> => {
    await p;
  };
  on(shutdown);
  const stop = (): undefined => undefined;
  on(stop);
  stop();
  on((): number => 0);
  const named = (event: string): string => event;
  onEvent(named);
  const echoed: string = named("SIGHUP");
}
