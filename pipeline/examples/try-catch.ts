// `try`: a throw may come from any point of the body, so the handler and the
// finalizer start from the cells' contracts, not from what the body wrote;
// the caught value is `unknown`, and a `typeof` test narrows it. A `throw`
// leaves the function unless a `try` catches it; the `finally` block runs on
// every way out, a `return` included, which then resumes.
function recover(mayThrow: () => void): number {
  let y: number | null = 1;
  try {
    y = 2;
    mayThrow();
  } catch (e) {
    const caught: unknown = e;
    y = 0;
  }
  if (y === null) {
    return -1;
  }
  return y;
}

function cleanup(mayThrow: () => void): boolean {
  let done: boolean = false;
  try {
    mayThrow();
  } finally {
    done = true;
  }
  return done;
}

function both(mayThrow: () => void): number {
  let y: number = 0;
  try {
    mayThrow();
    y = 1;
  } catch {
    y = 2;
  } finally {
    y = y + 1;
  }
  return y;
}

function returnsFromHandler(mayThrow: () => number): number {
  try {
    return mayThrow();
  } catch (e: unknown) {
    return 0;
  }
}

function raise(x: number | null): number {
  if (x === null) {
    throw "no value";
  }
  return x;
}

function handled(x: number | null): number {
  try {
    if (x === null) {
      throw x;
    }
    return x;
  } catch {
    return 0;
  }
}

function describe(f: () => string): string {
  try {
    return f();
  } catch (e) {
    if (typeof e === "string") {
      return e;
    }
    return "unknown";
  }
}

function rethrow(f: () => number): number {
  try {
    return f();
  } catch (e) {
    throw e;
  }
}

function returnThroughFinally(
  f: () => number,
  log: (n: number) => void,
): number {
  let seen: number = 0;
  try {
    return f();
  } finally {
    log(seen);
  }
}

function nested(f: () => number, g: () => void): number {
  try {
    try {
      return f();
    } finally {
      g();
    }
  } catch {
    return -1;
  }
}

function finallyOverrides(f: () => number): number {
  try {
    return f();
  } finally {
    return 0;
  }
}

async function awaited(p: Promise<number>): Promise<number> {
  try {
    return await p;
  } catch {
    return 0;
  }
}

function links(f: () => number, o: { a: number }): number {
  let c: number = 0;
  try {
    c = f();
    o.a = c;
  } catch (e) {
    c = o.a;
  } finally {
    o.a = 1;
  }
  return c;
}

function loopTry(xs: number[], f: (n: number) => number): number {
  let total: number = 0;
  for (const x of xs) {
    try {
      total = total + f(x);
    } catch {
      continue;
    }
  }
  return total;
}
