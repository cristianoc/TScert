// `on` returns the process: a reviewed method is readonly through the
// result as through `process`, so replacing `on` there is refused.
export function replace(listener: (code: number) => void): void {
  const registered = process.on("exit", listener);
  registered.on = () => registered;
}
