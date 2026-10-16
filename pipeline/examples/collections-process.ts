// Two reads of Node's `process`, apart from the library service:
// the platform constant and signal registration. A signal name that is only a
// `string` reaches `on`'s last overload; a literal one reaches the overload
// for `Signals`, whose listener is called with the signal's name.
const platform: "wasm" | "native" =
  process.env["APP_PLATFORM"] === "native" ? "native" : "wasm";
export function register(
  shutdown: (...args: unknown[]) => void,
  onSignal: (signal: string) => void,
): "wasm" | "native" {
  for (const sig of ["SIGTERM", "SIGINT"]) process.on(sig, shutdown);
  process.on("SIGHUP", onSignal).on("SIGUSR2", onSignal);
  return platform;
}
