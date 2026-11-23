// Counterexamples of the second review: decisions the prototype took beyond
// the paper's rules, each refused now. Each negative says whether its
// program is unsafe or only unprovable, and which rule refuses it.
type Footprint = { [location: string]: "keep" | "init" | "scalar" | "extend" | "grow" | "any" | true };
type AtMost<P extends Footprint> = Footprint;
type Visitor<E extends Footprint> = (i: number) => Modifies<E, void>;
type Counter = { n: number };

export function walk<E extends AtMost<{ "xs[*]": "keep"; else: "any" }>>(
  xs: number[],
  visit: Visitor<E>,
): number {
  const c = { i: 0 };
  let sum = 0;
  /** @invariant safeInteger(c.i) && 0 <= c.i */
  while (c.i < xs.length) {
    visit(c.i);
    sum += xs[c.i]!;
    c.i++;
  }
  return sum;
}

// 1. Negative, unsafe (Elem-Write): an array's `length` is its spine, so
// the write truncates the array the walker reads; it is no field `length`.
export function lengthWrite(xs: number[]): number {
  return walk<{ "xs.length": "any" }>(xs, () => {
    xs.length = 0;
  });
}

// 1. Negative, unsafe (Elem-Write): the same write through a string key.
export function lengthByKey(xs: number[]): number {
  return walk<{ "xs.length": "any" }>(xs, () => {
    xs["length"] = 0;
  });
}

// 1. Negative, unsafe (Push): `log` is no array; its member `push`
// truncates the array the walker reads.
export function pushObject(xs: number[]): number {
  const log = {
    push: (_: number): void => {
      xs.length = 0;
    },
  };
  return walk<{ "log[*]": "extend" }>(xs, (i) => {
    log.push(i);
  });
}

// 2. Negative, unsafe (Bound): the bound of F is not read, so the calls of
// its callback are bounded by nothing; the callback breaks `c.n`.
export function unreadBound<
  E extends AtMost<{}>,
  F extends AtMost<{ "c.n": "keep"; onThrow: true }>,
>(c: Counter, visit: (i: number) => Modifies<F, void>): void {
  visit(0);
}

/** @requires safeInteger(c.n) */
export function unreadBoundCaller(c: Counter, xs: number[]): number {
  if (0 <= c.n && c.n < xs.length) {
    unreadBound(c, () => {
      c.n = -1;
    });
    return xs[c.n]!;
  }
  return 0;
}

// 2. Negative, unsafe (the callback's type): the callback's type is not
// read, so the walker is refused, and so is a call of it with no instance.
export function unreadCallback<
  E extends AtMost<{ "c.n": "keep"; else: "any" }>,
>(
  c: Counter,
  visit: ((i: number) => Modifies<E, void>) | ((i: number) => Modifies<{ values: "any" }, void>),
): void {
  visit(0);
}

/** @requires safeInteger(c.n) */
export function unreadCallbackCaller(c: Counter, xs: number[]): number {
  if (0 <= c.n && c.n < xs.length) {
    unreadCallback(c, () => {
      c.n = -1;
    });
    return xs[c.n]!;
  }
  return 0;
}

// 3. Negative, unsafe (Inst's conclusion): the walker's own effect is keyed
// at `p`, which the walker reassigns to `q` before writing it.
export function reassigned<E extends AtMost<{}>>(
  p: Counter,
  q: Counter,
): void {
  p = q;
  p.n = -1;
}

/** @requires safeInteger(q.n) */
export function reassignedCaller(q: Counter, xs: number[]): number {
  if (0 <= q.n && q.n < xs.length) {
    const f = { n: 0 };
    reassigned(f, q);
    return xs[q.n]!;
  }
  return 0;
}

// 4. Negative, unsafe (the argument's type at Inst): the callback's
// parameter default writes `c.n` when the walker calls it with one argument.
/** @requires safeInteger(c.n) */
export function defaultWrite(c: Counter, xs: number[]): number {
  if (0 <= c.n && c.n < xs.length) {
    walk<{}>(xs, (i: number, z: number = (c.n = -1)) => {
      return;
    });
    return xs[c.n]!;
  }
  return 0;
}

// 4. Negative, unsafe (Inst's conclusion): the walker calls a local
// closure named as its callback; its effect is the walker's own.
export function shadowed<E extends AtMost<{ "p.n": "keep"; else: "any" }>>(
  p: Counter,
  xs: number[],
  visit: Visitor<E>,
): number {
  visit(0);
  {
    const visit = (): void => {
      p.n = -1;
    };
    visit();
  }
  return xs.length;
}

/** @requires safeInteger(p.n) */
export function shadowedCaller(p: Counter, xs: number[]): number {
  if (0 <= p.n && p.n < xs.length) {
    shadowed<{}>(p, xs, () => {
      return;
    });
    return xs[p.n]!;
  }
  return 0;
}

// 5. Negative (a signature holds for every call): the walker is held by a
// constant in a module importing it through a re-export
// (review2-reexporter.ts, review2-reimporter.ts).
export function walkRe<E extends AtMost<{ "xs[*]": "keep"; else: "any" }>>(
  xs: number[],
  visit: Visitor<E>,
): number {
  visit(0);
  return xs.length;
}

// 5. Negative (a signature holds for every call): the walker is held by a
// constant in a module of another directory (review2-dir/far.ts).
export function walkFar<E extends AtMost<{ "xs[*]": "keep"; else: "any" }>>(
  xs: number[],
  visit: Visitor<E>,
): number {
  visit(0);
  return xs.length;
}

// 6. Positive: an instance is the type argument at its effect parameter's
// position, after the ordinary type parameter `T`.
export function withValue<
  T,
  E extends AtMost<{ "c.n": "keep"; "value[*]": "keep"; else: "any" }>,
>(c: Counter, value: T, visit: Visitor<E>): T {
  visit(0);
  return value;
}

/** @requires safeInteger(c.n) */
export function withValueCaller(c: Counter, xs: number[]): number {
  if (0 <= c.n && c.n < xs.length) {
    withValue<number[], {}>(c, xs, () => {
      return;
    });
    return xs[c.n]!;
  }
  return 0;
}

// 7. Negative, only unprovable (decides less): a class key in a bound is
// not read.
export function classBound<
  E extends AtMost<{ values: "keep"; else: "any" }>,
>(xs: number[], visit: Visitor<E>): number {
  visit(0);
  return xs.length;
}
