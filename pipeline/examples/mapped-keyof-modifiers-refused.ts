// A mapped type over `keyof` writing no modifier copies its source's: `a`
// stays readonly and `b` optional, which the reader does not compute.
interface Source {
  readonly a: string;
  b?: string;
}

type Counts = { [K in keyof Source]: number };

export function count(c: Counts): number {
  return c.a;
}
