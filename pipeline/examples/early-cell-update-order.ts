// The evaluation order of updates and logical assignments of early
// bindings (run under Node): a compound assignment reads the cell before
// its right side, which writes the same cell, and writes the old value
// combined with the right side's; a logical assignment runs its right side
// and writes only on its writing branch; a postfix update's value is the
// old one; a local `let` a closure updates before its declaration is an
// early binding too.
let n: number = 1;
function reset(): number {
  n = 10;
  return 5;
}
export function compound(): number {
  n += reset();
  return n;
}

let calls: number = 0;
function side(): string {
  calls++;
  return "v";
}
let s: string | null = null;
let t: string = "";
let u: boolean = true;
function test(): boolean {
  calls++;
  return false;
}
export function logical(): string {
  const first = (s ??= side()) + (s ??= side());
  t ||= side();
  t ||= side();
  const second = t;
  u &&= test();
  u &&= test();
  return first + second + u + calls;
}

export function postfix(): number {
  const before = n++;
  return before * 100 + n;
}

export function local(): number {
  const inc = (): number => {
    return ++k;
  };
  const dec = (): number => {
    return k--;
  };
  let k: number = 0;
  inc();
  inc();
  const was = dec();
  return was * 10 + k;
}
