// Each resolving operation at a stable operand, beside a record whose `then`
// is callable, which the forged controls (`pipeline/test.mts`) substitute
// for the operand's instance: each is refused where evidence is produced and
// where it is checked.
const thenable = { then: (x: number): number => x };

export async function awaited(x: number): Promise<number> {
  return thenable.then(await x);
}

export async function returned(x: number): Promise<number> {
  return x;
}

export function resolved(x: number): Promise<number> {
  return Promise.resolve(x);
}

export function chained(p: Promise<number>): Promise<number> {
  return p.then((v) => v + 1);
}

export function recovered(p: Promise<number>): Promise<number> {
  return p.catch((reason: unknown) => 0);
}

export function cleaned(p: Promise<number>): Promise<number> {
  return p.finally(() => undefined);
}

export function made(): Promise<number> {
  return new Promise<number>((resolve: (value: number) => void) => resolve(1));
}

// An allocation with a callable `then`, called directly; forged as a
// `Promise<number>`, refused at the allocation.
export function local(): number {
  const own = { then: (x: number): number => x + 1 };
  return own.then(1);
}
