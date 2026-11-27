// Positive and negative cases for module-private confined state (`@state`,
// rule Confined in `Rules.lean` / `Model.lean` and `OwnerConfined` in
// `docs/drafts/abstract-confined-regions.md`):
// - Positives: unexported `let` lazy cache, `Record` cache, nested
//   `WeakMap<Prepared, Map<number, Int32Array>>` cache, walker calling a
//   confined helper, forwarding adapter with `[E, { "@state": "any" }]`, and
//   caller keeping handle facts across the walker.
// - Negatives: escaping container, parameter absorbed into `let` or `WeakMap`
//   and mutated, escaping nested interior, exported `let`, direct parameter
//   mutation claiming `@state`, `subarray` stored into mutated cache, and
//   `@state` passed to a walker whose bound has `else: "keep"`.
type Footprint = { [location: string]: "keep" | "init" | "scalar" | "extend" | "grow" | "any" | true };
type AtMost<P extends Footprint> = Footprint;
type Effects<P extends Footprint, T> = T;
type Join<E extends Footprint, P extends Footprint> = Footprint;
type LineVisitor<E extends Footprint> = (width: number) => Modifies<E, void>;
type Prepared = { widths: number[]; flags: number[] };
type Cursor = { segmentIndex: number };

// --- Positive confined caches ---

let cachedBias: { value: number } | null = null;
function getBias(): Modifies<{ values: "init" }, Effects<{ "@state": "any" }, { value: number }>> {
  return cachedBias ??= { value: 1 };
}

type RuleKey = "a" | "k";
const ruleCache: Partial<Record<RuleKey, number>> = {};
function lookupRule(key: RuleKey): Effects<{ "@state": "any" }, number> {
  const hit = ruleCache[key];
  if (hit !== undefined) return hit;
  const fresh = key.length;
  ruleCache[key] = fresh;
  return fresh;
}

const nestedCaches = new WeakMap<Prepared, Map<number, Int32Array>>();
function getCachedSlots(p: Prepared, idx: number): Effects<{ "@state": "any" }, Int32Array> {
  let inner = nestedCaches.get(p);
  if (inner === undefined) {
    inner = new Map<number, Int32Array>();
    nestedCaches.set(p, inner);
  }
  let slots = inner.get(idx);
  if (slots === undefined) {
    slots = new Int32Array(2);
    slots[0] = idx;
    inner.set(idx, slots);
  }
  return slots;
}

// Positive: walker whose own body calls a confined-state helper (`getBias`)
// keeps `Bound`'s second premise because `@state` is disjoint from `prepared.**`.
export function walkLines<E extends AtMost<{ "prepared.**": "keep"; else: "any" }>>(
  prepared: Prepared, onLine: LineVisitor<E>): number {
  const bias = getBias().value;
  const cursor: Cursor = { segmentIndex: 0 };
  let total = 0;
  /** @invariant safeInteger(cursor.segmentIndex) && 0 <= cursor.segmentIndex */
  while (cursor.segmentIndex < prepared.widths.length) {
    const start = cursor.segmentIndex;
    onLine(prepared.widths[start]! + bias);
    total += prepared.widths[cursor.segmentIndex]! >= 0 ? 1 : 0;
    cursor.segmentIndex = start + 1;
  }
  return total;
}

// Positive: visitor mutates fresh `out` plus confined `let`, `Record`, and
// nested `WeakMap<Prepared, Map<number, Int32Array>>` caches.
/** @requires safeInteger(i) && 0 <= i */
export function collectWithCaches(p: Prepared, i: number): number {
  if (p.flags.length !== p.widths.length) return 0;
  const out: number[] = [];
  walkLines<{ "out[*]": "extend"; "@state": "any" }>(p, (w) => {
    const s = getCachedSlots(p, 0);
    out.push(w + lookupRule("k") + (s[0] ?? 0));
  });
  if (i < p.widths.length) return p.flags[i]!;
  return 0;
}

// Positive: forwarding adapter with `Join<E, { "@state": "any" }>`.
export function walkAdapter<E extends AtMost<{ "prepared.**": "keep"; else: "any" }>>(
  prepared: Prepared, onLine: LineVisitor<E>): number {
  return walkLines<Join<E, { "@state": "any" }>>(prepared, (w) => {
    const extra = lookupRule("a");
    onLine(w + extra);
  });
}

// --- Negative controls (all must be refused) ---

// Negative 1 (unsafe / confinement violation): container escapes via return.
const leakedRecord: Record<string, number> = {};
export function leakRecord(): Record<string, number> { return leakedRecord; }
export function writeLeakedRecord(): Effects<{ "@state": "any" }, void> {
  leakedRecord["x"] = 1;
}

// Negative 2 (unsafe / confinement violation): `let` absorbs a parameter and is mutated through.
let stashedArr: number[] | null = null;
export function absorbIntoLet(xs: number[]): void { stashedArr = xs; }
export function mutateStashedLet(): Effects<{ "@state": "any" }, void> {
  if (stashedArr !== null) stashedArr.push(0);
}

// Negative 3 (unsafe / confinement violation): `WeakMap` absorbs a caller array and mutates it on retrieval.
const badMap = new WeakMap<Prepared, number[]>();
export function absorbIntoMap(p: Prepared, xs: number[]): void { badMap.set(p, xs); }
export function mutateAbsorbedMap(p: Prepared): Effects<{ "@state": "any" }, void> {
  const a = badMap.get(p);
  if (a !== undefined) a.push(0);
}

// Negative 4 (unsafe / confinement violation): nested interior escapes via return.
const leakyNested = new WeakMap<Prepared, Map<number, number>>();
export function leakNestedInner(p: Prepared): Map<number, number> | undefined { return leakyNested.get(p); }
export function writeLeakyNested(p: Prepared): Effects<{ "@state": "any" }, void> {
  let m = leakyNested.get(p);
  if (m === undefined) { m = new Map<number, number>(); leakyNested.set(p, m); }
  m.set(0, 1);
}

// Negative 5 (confinement violation): exported `const` container is not module-private.
export const exportedCache: Record<string, number> = {};
export function writeExported(): Effects<{ "@state": "any" }, void> {
  exportedCache["a"] = 1;
}

// Negative 6 (unsafe): function claims `@state` while mutating parameter `p`.
export function lieAboutParam(p: Prepared): Effects<{ "@state": "any" }, void> {
  p.widths.push(0);
}

// Negative 7 (unsafe / subarray aliasing): `subarray` shares caller's buffer and is mutated in cache.
const badViews = new WeakMap<Prepared, Int32Array>();
export function absorbSubarray(p: Prepared, src: Int32Array): void { badViews.set(p, src.subarray(0)); }
export function mutateSubarrayCache(p: Prepared): Effects<{ "@state": "any" }, void> {
  const v = badViews.get(p);
  if (v !== undefined) v[0] = 99;
}

// Negative 8 (unprovable / bound violation): `@state: any` violates `else: "keep"`.
export function walkPure<E extends AtMost<{ else: "keep" }>>(
  prepared: Prepared, onLine: LineVisitor<E>): number {
  if (prepared.widths.length > 0) onLine(prepared.widths[0]!);
  return prepared.widths.length;
}
export function callPureWithState(p: Prepared): number {
  return walkPure<{ "@state": "any" }>(p, () => { lookupRule("k"); });
}

// Negative 9 (unsafe / non-host method name): user-defined `appendChild` is
// not a DOM host method and may mutate caller state, so `@state` must be refused.
interface Box { log: number[]; appendChild(n: number): void }
export function callUserAppendChild(b: Box): Effects<{ "@state": "any" }, void> {
  b.appendChild(1);
}

// Negative 10 (confinement violation): exported stateful `RegExp` is not module-private,
// so mutating its `lastIndex` via `replace` is not confined to `@state`.
export const exportedRe = /a/g;
export function matchExportedRe(s: string): Effects<{ "@state": "any" }, string> {
  return s.replace(exportedRe, "b");
}

// Negative 11 (unsafe / non-string receiver): user-defined `.replace` on an object
// is not `String.prototype.replace`, so `@state` must be refused.
interface Replacer { replace(re: RegExp, s: string): string }
export function callUserReplace(r: Replacer): Effects<{ "@state": "any" }, string> {
  return r.replace(/a/, "b");
}

// Negative 12 (unsafe / shadowed typed array type): a local `type Uint16Array = number[]`
// shadows the built-in typed array, so writing an element is not covered by `views: "grow"`.
type Uint16Array = number[];
function getFakeTyped(xs: Uint16Array): Effects<{ else: "keep" }, Uint16Array> { return xs; }
export function writeShadowedTyped(xs: Uint16Array): Effects<{ views: "grow" }, void> {
  getFakeTyped(xs)[0] = 1;
}
