// A shift left past the signed 32-bit range: 8388608 << 8 is -2147483648, so
// the test `y < values.length` passes and the read is below 0.
// Shl states y = 256 * hi only where -2^31 <= 256 * hi < 2^31; here hi may
// be 8388608, and 256 * hi = 2^31.
/** @requires safeInteger(hi) && 0 <= hi && hi <= 8388608 */
export function shifted(values: Uint8Array, hi: number): number {
  const y = hi << 8;
  if (y < values.length) return values[y]!;
  return 0;
}
