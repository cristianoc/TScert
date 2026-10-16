// Variadic closure offering without the unrelated async-library assumption.
function on(listener: (...args: unknown[]) => void): void {
  listener("SIGTERM", 1);
}
function onEvent(listener: (event: string, ...rest: unknown[]) => void): void {
  listener("SIGINT");
}
export function register(): void {
  const stop = (): undefined => undefined;
  on(stop);
  stop();
  on((): number => 0);
  const named = (event: string): string => event;
  onEvent(named);
  const echoed: string = named("SIGHUP");
}
