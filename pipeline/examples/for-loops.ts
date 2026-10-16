// `for (init; cond; update) body`: the loop's update runs at the end of the
// body and at every `continue`; a `let` declared in `init` is scoped to the
// loop, so two loops may declare the same name.
function sum(n: number): number {
  let total: number = 0;
  for (let i: number = 0; i < n; i = i + 1) {
    total = total + i;
  }
  for (let i: number = 0; i < n; i = i + 1) total = total + i;
  return total;
}

function skipping(n: number, skip: boolean): number {
  let total: number = 0;
  for (let i: number = 0; i < n; i = i + 1) {
    if (skip) {
      continue;
    }
    total = total + 1;
  }
  return total;
}

function forever(flag: boolean): boolean {
  let seen: boolean = false;
  for (;;) {
    if (flag) {
      break;
    }
    seen = true;
  }
  return seen;
}

function noInit(x: number | null, again: boolean): number {
  let y: number | null = x;
  for (; again; y = null) {
    if (y !== null) {
      return y;
    }
  }
  return 0;
}

// An unannotated `let` before a `for`: its contract is claimed at the first
// statement that runs next, the loop's initializer, as a block has no entry
// of its own.
function unannotated(n: number): number {
  let total = 0;
  for (let i = 0; i < n; i = i + 1) {
    total = total + i;
  }
  return total;
}

// A nested block is a scope of its own.
function blocks(x: number): number {
  {
    const y: number = x;
    x + y;
  }
  const y: number = 1;
  return y;
}
