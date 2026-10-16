// `Math.max` and `Math.min` of numbers written out and spread from arrays, a
// readable array whose holes the spread reads as `undefined` included, and of
// no argument (`-Infinity`, `Infinity`); `String.fromCodePoint` and
// `String.fromCharCode` likewise.
export function widest(widths: number[]): number {
  return Math.max(0, ...widths);
}

export function clamp(x: number, low: number, high: number): number {
  return Math.min(Math.max(x, low), high);
}

export function bounds(xs: readonly number[]): [number, number] {
  return [Math.min(...xs), Math.max(...xs)];
}

export function extremes(): number {
  return Math.max() - Math.min();
}

export function decode(points: readonly number[], first: number): string {
  return String.fromCodePoint(first, ...points);
}

export function units(codes: number[]): string {
  return String.fromCharCode(...codes) + String.fromCharCode();
}
