/** The original repair regression: only a nullish parameter is overwritten. */
function localFallback(value: number | null): number {
  value ??= 1;
  return value;
}

/** A non-nullish Boolean, including false, must skip every RHS effect. */
function skippedFallback(value: boolean | undefined): boolean {
  let touched: boolean = false;
  const result = (value ??= touched = true);
  return touched;
}

/** Nested fallbacks must preserve both assignment results and slot indices. */
function nestedFallback(
  left: number | null,
  right: number | undefined,
): number {
  const result = (left ??= right ??= 2);
  return result;
}

/** An escaping callback retains the location, rather than a creation-time read. */
function capturedFallback(value: number | null): () => number {
  return (): number => (value ??= 3);
}
