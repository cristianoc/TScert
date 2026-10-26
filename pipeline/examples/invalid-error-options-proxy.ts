// A proxy's `has` trap, which `Error` runs through `HasProperty`: client code
// that shrinks the array `map` visits. Refused at the proxy.
export function wrong(xs: string[]): string[] {
  const options = new Proxy(
    {},
    {
      has: () => {
        xs.pop();
        return false;
      },
    },
  );
  return xs.map((x) => Error(x, options).message);
}
