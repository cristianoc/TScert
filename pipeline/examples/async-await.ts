// `await` yields what a promise settles to, at its type argument; an async
// function's call returns a promise of what its body returns, or of
// `undefined` when it completes. Async arrows alike, and the module's own
// code may await.
export async function settled(p: Promise<number>): Promise<number> {
  const n: number = await p;
  return n;
}
async function wait(p: Promise<boolean>): Promise<void> {
  await p;
}
export function later(p: Promise<string>): () => Promise<string> {
  return async (): Promise<string> => await p;
}
export function block(p: Promise<boolean>): () => Promise<void> {
  const f = async (): Promise<void> => {
    await wait(p);
  };
  return f;
}
export async function chained(p: Promise<number>): Promise<number> {
  const read = (): Promise<number> => p;
  return await settled(read());
}
async function start(): Promise<boolean> {
  return true;
}
// Awaiting a primitive yields it, as does awaiting a union of a promise and
// primitives; an async function may return a promise of a primitive, which
// its own promise adopts.
export async function passes(n: number): Promise<number> {
  return await n;
}
export async function either(
  b: boolean,
  p: Promise<number>,
  n: number,
): Promise<number> {
  const x = b ? p : n;
  return await x;
}
export async function forwards(p: Promise<string>): Promise<string> {
  return p;
}
export function forwardsLater(p: Promise<number>): () => Promise<number> {
  return async () => p;
}
const started: boolean = await start();
await wait(start());
