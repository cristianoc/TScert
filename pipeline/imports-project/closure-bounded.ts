// Const-bound callable contract, as in pretext's module helpers.
/** @requires safeInteger(i) && 0 <= i && i < xs.length */
export const at = (xs: number[], i: number): number => xs[i]!;
