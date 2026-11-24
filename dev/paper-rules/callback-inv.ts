// Tests for rule Callback-Inv (scoped callback invariant) and framing across
// monomorphic `Effects<P, T>` helpers calling quantified walkers with omitted
// callbacks and null optional parameters:
// - Positive: inline closures passed to non-escaping quantified walkers
//   (`collectWithLines`, `walkRichRanges`), plus `countLines` / `stepLine`
//   framing across `Effects<..., ...>` calls.
// - Negative (all 4 unsound closure-capture counterexamples, each refused):
//   1. `mutateBeforeCall`: mutates handle before calling the walker;
//   2. `badWalker` / `callBadWalker`: walker mutates handle before invoking cb;
//   3. `callStashWalker`: walker escapes cb into module state;
//   4. `callSelfMutating`: callback itself mutates the handle;
//   5. `callViaAlias`: stores closure in a local, mutates handle, then calls.

type Footprint = {
  [location: string]:
    | "keep"
    | "init"
    | "scalar"
    | "extend"
    | "grow"
    | "any"
    | true;
};
type AtMost<P extends Footprint> = Footprint;
type Effects<P extends Footprint, T> = T;
type Join<E extends Footprint, P extends Footprint> = Footprint;

type Visitor<E extends Footprint> = (i: number) => Modifies<E, void>;

/** @invariant this.segmentFlags.length === this.widths.length */
export type Prepared = {
  widths: number[];
  segmentFlags: Uint8Array;
};

/** @invariant this.data.segmentFlags.length === this.data.widths.length */
export type RichHandle = {
  data: Prepared;
  tag: number;
};

export type Cursor = {
  index: number;
};

export type Stats = {
  count: number;
};

let bias: number = 0;

function getBias(): Effects<{ "@state": "any" }, number> {
  bias += 1;
  return bias;
}

function readFlag(
  p: Prepared,
  i: number,
): Effects<{ "@state": "any" }, number> {
  const b = getBias();
  return Number.isSafeInteger(i) && i >= 0 && i < p.widths.length
    ? p.segmentFlags[i]! + b
    : b;
}

function readRichFlag(
  flow: RichHandle,
  i: number,
): Effects<{ "@state": "any" }, number> {
  return readFlag(flow.data, i) + flow.tag;
}

function idRich(flow: RichHandle): RichHandle {
  return flow;
}

function walkPreparedInner<E extends AtMost<{ "p.**": "keep"; else: "any" }>>(
  p: Prepared,
  cursor: Cursor,
  onItem: Visitor<E> | undefined,
  stats: Stats | null,
): number {
  const b = getBias();
  let total = b;
  const n = p.widths.length;
  /** @invariant safeInteger(i) && safeInteger(n) && 0 <= i && p.segmentFlags.length === n && p.widths.length === n */
  for (let i = 0; i < n; i++) {
    total += p.segmentFlags[i]!;
    cursor.index = i;
    if (stats !== null) stats.count += 1;
    onItem?.(i);
  }
  return total;
}

export function walkPreparedForward<
  E extends AtMost<{ "p.**": "keep"; else: "any" }>,
>(p: Prepared, onItem?: Visitor<E>, stats: Stats = { count: 0 }): number {
  const cursor: Cursor = { index: 0 };
  return walkPreparedInner<E>(p, cursor, onItem, stats);
}

// Positive: monomorphic `Effects<{ "@state": "any" }, number>` calling a
// quantified walker with omitted callback and omitted fresh-default `stats`.
export function countLines(p: Prepared): Effects<{ "@state": "any" }, number> {
  return walkPreparedForward(p);
}

// Positive: monomorphic `Effects` calling a quantified walker with explicit
// `undefined` callback and `null` optional `stats`.
export function stepLine(
  p: Prepared,
  cursor: Cursor,
): Effects<{ "@state": "any"; "cursor.index": "any" }, number> {
  return walkPreparedInner(p, cursor, undefined, null);
}

// Positive: caller's type invariant on `p` survives `countLines(p)` via Confined.
export function useCountLines(p: Prepared): number {
  const n = countLines(p);
  return n + readFlag(p, 0);
}

// Positive: caller's type invariant on `p` survives `stepLine(p, cursor)` via Confined.
export function useStepLine(p: Prepared, cursor: Cursor): number {
  const n = stepLine(p, cursor);
  return n + readFlag(p, 0);
}

// Positive (Callback-Inv, layoutWithLines shape): inline callback captures `p`,
// calls `readFlag(p, i)` requiring `p`'s invariant, extends fresh `out`.
export function collectWithLines(p: Prepared): number[] {
  const out: number[] = [];
  walkPreparedForward<{ "out[*]": "extend"; "@state": "any" }>(p, (i) => {
    out.push(readFlag(p, i));
  });
  return out;
}

// Positive (Callback-Inv, walkRichInlineLineRanges shape): inline callback
// captures `local` (aliased to `flow` via `idRich`) under `Join<E, { "@state": "any" }>`,
// calls `readRichFlag(local, i)` requiring `local.data`'s invariant, then `onLine`.
export function walkRichRanges<
  E extends AtMost<{ "flow.**": "keep"; else: "any" }>,
>(flow: RichHandle, onLine: (v: number) => Modifies<E, void>): number {
  const local = idRich(flow);
  const data = local.data;
  return walkPreparedForward<Join<E, { "@state": "any" }>>(data, (i) => {
    onLine(readRichFlag(local, i));
  });
}

// Negative 1 (mutate before call): breaks `p`'s invariant before calling walker.
export function mutateBeforeCall(p: Prepared): number {
  p.widths.push(0);
  return walkPreparedForward<{ "@state": "any" }>(p, (i) => {
    readFlag(p, i);
  });
}

// Negative 2 (callee mutates before invoking callback): breaks Rule Bound's 2nd premise.
export function badWalker<E extends AtMost<{ "p.**": "keep"; else: "any" }>>(
  p: Prepared,
  onItem: Visitor<E>,
): number {
  p.widths.push(0);
  onItem(0);
  return p.widths.length;
}

export function callBadWalker(p: Prepared): number {
  return badWalker<{ "@state": "any" }>(p, (i) => {
    readFlag(p, i);
  });
}

// Negative 3 (callee escapes callback into module state): `stashWalker` fails
// non-escape check, so `Callback-Inv` does not apply to `callStashWalker`.
let savedVisitor: ((i: number) => void) | null = null;

export function stashWalker<E extends AtMost<{ "p.**": "keep"; else: "any" }>>(
  p: Prepared,
  onItem: Visitor<E>,
): number {
  savedVisitor = onItem;
  return p.widths.length;
}

export function callStashWalker(p: Prepared): number {
  return stashWalker<{ "@state": "any" }>(p, (i) => {
    readFlag(p, i);
  });
}

// Negative 4 (callback mutates `p` itself): fails Inst against `"p.**": "keep"`.
export function callSelfMutating(p: Prepared): number {
  return walkPreparedForward<{ "p.widths[*]": "extend"; "@state": "any" }>(
    p,
    (i) => {
      readFlag(p, i);
      p.widths.push(0);
    },
  );
}

// Negative 5 (closure stored in local alias, handle mutated before call).
export function callViaAlias(p: Prepared): number {
  const cb = (i: number) => {
    readFlag(p, i);
  };
  p.widths.push(0);
  return walkPreparedForward<{ "@state": "any" }>(p, cb);
}
