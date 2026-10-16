// An array cannot replace the constructor used by copying native methods.
export function replace(xs: number[], replacement: Function): void {
  xs.constructor = replacement;
}
