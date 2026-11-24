// Regression tests for eliminating the #355 and #364 assumes in Pretext's
// complex line walker (`walkPreparedComplexLines` / `walkPreparedLinesRaw`):
// 1. Confined `Effects<{ "@state": "any" }, T>` helper calls preserve external
//    read links (`const { xs } = h`) before a bounded-callback loop (#364).
// 2. Alias-aware bound coverage in `PaperRulesPrototype.keepsPair` preserves
//    `"cursor.segmentIndex": "keep"` when `cursor` is aliased at the call site,
//    and polymorphic forwarding (`walkCursor<E>`) discharges own-location bound
//    entries on a caller-allocated `const` object via rules Anch + Meet (#355).
// 3. `SinglePass.nearStep` filters non-linear index atoms so guarded/disjunctive
//    facts cannot crowd out linear chains during merge entailment (#355).

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

type Visitor<E extends Footprint> = (v: number) => Modifies<E, void>;
type CursorVisitor<E extends Footprint> = (v: number, seg: number) => Modifies<E, void>;

/** @invariant this.ys.length === this.xs.length */
type Handle = { xs: number[]; ys: Uint8Array };
type Cursor = { segmentIndex: number };
type Profile = { eps: number };

let cachedProfile: Profile | null = null;
function getProfile(): Modifies<{ values: "init" }, Effects<{ "@state": "any" }, Profile>> {
  return cachedProfile ??= { eps: 1 };
}

/** @requires safeInteger(cursor.segmentIndex) && 0 <= cursor.segmentIndex
 *  @ensures safeInteger(cursor.segmentIndex) && 0 <= cursor.segmentIndex
 *  @ensures result === false || cursor.segmentIndex < h.xs.length */
function normalizeCursor(
  h: Handle,
  cursor: Cursor,
): Modifies<{ "cursor.segmentIndex": "scalar" }, boolean> {
  if (cursor.segmentIndex >= h.xs.length) return false;
  return true;
}

// Positive (#364): `getProfile()` is verified `Effects<{ "@state": "any" }, Profile>`,
// so the destructured read link `xs = h.xs` survives `getProfile()`, enters the loop
// head, and lets `onStep?.(v)` keep `xs.length === n` under `"h.**": "keep"`.
export function walkDestructuredConfined<E extends AtMost<{ "h.**": "keep"; else: "any" }>>(
  h: Handle,
  onStep?: Visitor<E>,
): number {
  const { xs, ys } = h;
  const n = xs.length;
  const profile = getProfile();
  let i = 0;
  let total = profile.eps;
  /** @invariant safeInteger(i) && safeInteger(n) && 0 <= i && xs.length === n && ys.length === n */
  while (true) {
    if (i >= n) return total;
    const v = xs[i]!;
    total += v;
    onStep?.(v);
    i++;
  }
}

// Negative, unsafe (#364): without `"h.**": "keep"`, `onStep` may pop `h.xs`
// and invalidate `xs.length === n`.
export function walkDestructuredUnbounded<E extends AtMost<{ else: "any" }>>(
  h: Handle,
  onStep?: Visitor<E>,
): number {
  const { xs, ys } = h;
  const n = xs.length;
  const profile = getProfile();
  let i = 0;
  let total = profile.eps;
  /** @invariant safeInteger(i) && safeInteger(n) && 0 <= i && xs.length === n && ys.length === n */
  while (true) {
    if (i >= n) return total;
    const v = xs[i]!;
    total += v;
    onStep?.(v);
    i++;
  }
}

// Positive (#355): `"cursor.segmentIndex": "keep"` survives `onStep?.(v, cursor.segmentIndex)`
// even when evaluating `cursor.segmentIndex` aliases `cursor` to a fresh slot.
/** @requires safeInteger(cursor.segmentIndex) && 0 <= cursor.segmentIndex && cursor.segmentIndex < h.xs.length
 *  @ensures safeInteger(cursor.segmentIndex) && 0 <= cursor.segmentIndex */
export function walkCursor<E extends AtMost<{ "h.**": "keep"; "cursor.segmentIndex": "keep"; else: "any" }>>(
  h: Handle,
  cursor: Cursor,
  onStep?: CursorVisitor<E>,
): number {
  const { xs, ys } = h;
  const n = xs.length;
  const profile = getProfile();
  let total = profile.eps;
  /** @invariant safeInteger(cursor.segmentIndex) && safeInteger(n) && 0 <= cursor.segmentIndex && cursor.segmentIndex < n && ys.length === n && xs.length === n */
  while (true) {
    const start = cursor.segmentIndex;
    const v = xs[start]!;
    total += v;
    cursor.segmentIndex = start + 1;
    onStep?.(v, cursor.segmentIndex);
    if (!normalizeCursor(h, cursor)) break;
  }
  return total;
}

// Negative, unsafe (#355): without `"cursor.segmentIndex": "keep"`, `onStep` may
// set `cursor.segmentIndex = -1`, violating `normalizeCursor`'s precondition.
/** @requires safeInteger(cursor.segmentIndex) && 0 <= cursor.segmentIndex && cursor.segmentIndex < h.xs.length
 *  @ensures safeInteger(cursor.segmentIndex) && 0 <= cursor.segmentIndex */
export function walkCursorUnbounded<E extends AtMost<{ "h.**": "keep"; else: "any" }>>(
  h: Handle,
  cursor: Cursor,
  onStep?: CursorVisitor<E>,
): number {
  const { xs, ys } = h;
  const n = xs.length;
  let total = 0;
  /** @invariant safeInteger(cursor.segmentIndex) && safeInteger(n) && 0 <= cursor.segmentIndex && cursor.segmentIndex < n && ys.length === n && xs.length === n */
  while (true) {
    const start = cursor.segmentIndex;
    const v = xs[start]!;
    total += v;
    cursor.segmentIndex = start + 1;
    onStep?.(v, cursor.segmentIndex);
    if (!normalizeCursor(h, cursor)) break;
  }
  return total;
}

// Positive (#355): forwarding outer `E` to `walkCursor<E>` with a fresh local
// `const cursor` discharges `"cursor.segmentIndex": "keep"` via rules Anch + Meet.
export function outerForwardFresh<E extends AtMost<{ "h.**": "keep"; else: "any" }>>(
  h: Handle,
  onStep?: CursorVisitor<E>,
): number {
  const cursor: Cursor = { segmentIndex: 0 };
  if (!normalizeCursor(h, cursor)) return 0;
  return walkCursor<E>(h, cursor, onStep);
}

// Negative, unsafe (#355): `cursor` is a parameter (existed at entry), so Anch
// does not protect it; the caller's callback for `E` may mutate `cursor.segmentIndex`.
export function outerForwardParam<E extends AtMost<{ "h.**": "keep"; else: "any" }>>(
  h: Handle,
  cursor: Cursor,
  onStep?: CursorVisitor<E>,
): number {
  if (!normalizeCursor(h, cursor)) return 0;
  return walkCursor<E>(h, cursor, onStep);
}

// Negative, unsafe (#355): `let cursor` reassigned from parameter `other` is not
// a fresh `const` allocation, so Anch does not discharge `"cursor.segmentIndex": "keep"`.
export function outerForwardLet<E extends AtMost<{ "h.**": "keep"; else: "any" }>>(
  h: Handle,
  other: Cursor,
  onStep?: CursorVisitor<E>,
): number {
  let cursor: Cursor = { segmentIndex: 0 };
  cursor = other;
  if (!normalizeCursor(h, cursor)) return 0;
  return walkCursor<E>(h, cursor, onStep);
}

// Negative, unsafe (#355): forwarding `Join<E, { "cursor.segmentIndex": "any" }>`
// allows the local closure itself to mutate `cursor.segmentIndex`, which violates
// `walkCursor`'s bound despite `cursor` being fresh.
export function outerForwardJoinMutates<E extends AtMost<{ "h.**": "keep"; else: "any" }>>(
  h: Handle,
  onStep?: CursorVisitor<E>,
): number {
  const cursor: Cursor = { segmentIndex: 0 };
  if (!normalizeCursor(h, cursor)) return 0;
  return walkCursor<Join<E, { "cursor.segmentIndex": "any" }>>(h, cursor, (v, s) => {
    cursor.segmentIndex = -1;
    onStep?.(v, s);
  });
}

// Negative, unsafe (#355): nested field through a fresh `const` wrapper may alias
// an older parameter (`inner`), so Anch only covers own locations, not `box.inner.segmentIndex`.
type Box = { inner: Cursor };

function walkNested<E extends AtMost<{ "box.inner.segmentIndex": "keep"; else: "any" }>>(
  box: Box,
  onStep?: Visitor<E>,
): void {
  onStep?.(box.inner.segmentIndex);
}

export function outerForwardNested<E extends AtMost<{ else: "any" }>>(
  inner: Cursor,
  onStep?: Visitor<E>,
): void {
  const box: Box = { inner };
  walkNested<E>(box, onStep);
}
