// A mapped type over `keyof` writing no readonly modifier copies `a`'s:
// a write through it is refused, though an alias writing `-readonly` admits one.
interface Source {
  readonly a: string;
}

type Counts = { [K in keyof Source]: number };

export function write(c: Counts): void {
  (c as { a: number }).a = 1;
}
