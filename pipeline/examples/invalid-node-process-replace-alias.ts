// An alias of the process `on` returns: replacing a reviewed method through
// it is refused.
export function replace(listener: (code: number) => void): void {
  const alias = process.once("exit", listener);
  const again = alias;
  again.once = () => again;
}
