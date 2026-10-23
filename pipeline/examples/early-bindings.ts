// A `let` or `const` a closure created before its declaration reads, or one
// mentioned above its declaration, is an early binding: a cell from the
// entry of its block, holding the uninitialized marker until its
// declaration writes it, every mention a checked access that throws where
// it is uninitialized (SOURCE-ELABORATION.md, "Lexical bindings before
// initialization").

// A closure reading a constant declared after it, called after both.
export function count(xs: number[]): number {
  let found = 0;
  const visit = (x: number): void => {
    if (wanted(x)) found++;
  };
  const wanted = (x: number): boolean => x > 10;
  for (const x of xs) visit(x);
  return found;
}

// An early `let`, assigned after its declaration: the closure reads its
// current contents.
export function later(): number {
  const get = (): number => n;
  let n: number = 1;
  n = 2;
  return get();
}

// A call before the declaration runs: the checked access throws there.
export function tooSoon(): number {
  const get = (): number => n;
  const x = get();
  const n: number = 1;
  return x + n;
}

// A block entered once per iteration: each entry has its own binding.
export function perIteration(xs: number[]): number {
  let total = 0;
  for (const x of xs) {
    const add = (): number => y;
    const y: number = x;
    total += add();
  }
  return total;
}

// `typeof` of an early binding is a checked access too.
export function kind(): boolean {
  const test = (): boolean => typeof v === "number";
  const v: number = 1;
  return test();
}

// An early binding holding an object, read in closure term code: its
// checked access may find either, and calls the intrinsic at its own type.
export function boxed(): number {
  const get = (): number => box.n;
  const box: { n: number } = { n: 1 };
  return get();
}
