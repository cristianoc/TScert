// A binding held in a cell keeps its narrowed contents across a call or a
// loop only where nothing can change them: a function literal assigning
// `refused`, called in a loop, leaves it `boolean` at the loop's head and
// after it; a module cell narrowed by a test is `boolean` again after a
// call that may change a value.
// A cell keeps its narrowing across a loop with no call and across a write
// of another key.
// Census functions:
// guard-closure.mts#guardClosure, declaration-session.mts#collect.
let flag: boolean = false;
export function set(on: boolean): void {
  flag = on;
}
function touch(o: { n: number }): number {
  o.n++;
  return o.n;
}
export function refusedAny(xs: string[]): boolean {
  let refused = false;
  const visit = (s: string): void => {
    if (s === "x") refused = true;
  };
  for (const x of xs) visit(x);
  return refused;
}
export function counted(o: { n: number }): number {
  let r = 0;
  if (!flag) {
    r = 1;
  } else {
    const k = touch(o);
    if (k > 3) r = 2;
    else r = 3;
  }
  return r;
}
let cache: Map<string, number> | null = null;
export function reset(): void {
  cache = new Map();
}
export function summed(xs: number[]): number {
  if (cache === null) return 0;
  let t = 0;
  for (let i = 0; i < xs.length; i++) t += i;
  return t + cache.size;
}
export function written(o: { n: number }): number {
  if (cache === null) return 0;
  o.n = 1;
  return cache.size;
}
