// A function declaration in a body or a block is bound when its block is
// entered: a constant holding its closure, created before the first
// statement that may read it (SOURCE-ELABORATION.md, "Function declarations
// in a body"; each run under Node).

// A call above the declaration: the closure exists from the block's entry.
export function hoisted(): number {
  const r = twice(2);
  function twice(n: number): number {
    return n * 2;
  }
  return r;
}

// Recursion through the declaration's own name.
export function factorial(n: number): number {
  function go(k: number): number {
    return k <= 1 ? 1 : k * go(k - 1);
  }
  return go(n);
}

// Mutual recursion: `isEven` mentions `isOdd`, bound after it.
export function parity(n: number): boolean {
  return isEven(n);
  function isEven(k: number): boolean {
    if (k === 0) return true;
    return isOdd(k - 1);
  }
  function isOdd(k: number): boolean {
    if (k === 0) return false;
    return isEven(k - 1);
  }
}

// A declaration reading a constant declared above it, called from a closure
// created before the declaration, and after the constant is initialized.
export function filtered(xs: string[], omit: string[]): string[] {
  const omitted = new Set(omit);
  const each = (x: string): string[] => keep(x);
  function keep(x: string): string[] {
    return omitted.has(x) ? [] : [x];
  }
  const out: string[] = [];
  for (const x of xs) for (const y of each(x)) out.push(y);
  return out;
}

// Declarations reading a constant declared after them, which holds them: the
// constant is an early binding, initialized before either is called.
type Pair = { left: (n: number) => number; right: (n: number) => number };
export function pair(n: number): number {
  function left(k: number): number {
    if (k > 0) return both.right(k - 1);
    return 0;
  }
  function right(k: number): number {
    if (k > 0) return both.left(k - 1) + 1;
    return 0;
  }
  const both: Pair = { left, right };
  return both.left(n);
}

// A declaration in a nested block of a module, which is strict: the block's
// own binding.
export function inBlock(flag: boolean): number {
  if (flag) {
    function one(): number {
      return 1;
    }
    return one();
  }
  return 0;
}
