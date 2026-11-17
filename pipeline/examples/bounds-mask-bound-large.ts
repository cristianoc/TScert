// Mask's bound for an operand past 2^31: `x & 0x7fffffff` is at most x for
// every safe integer 0 <= x, so it indexes an array longer than x.
/** @requires safeInteger(x) && 0 <= x && x < values.length */
export function lowBits(values: Uint8Array, x: number): number {
  return values[x & 0x7fffffff]!;
}
