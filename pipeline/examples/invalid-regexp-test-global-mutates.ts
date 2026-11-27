// A global regex's `test` mutates its own `lastIndex` (`{this.lastIndex: scalar}`),
// so a function calling it does not meet the empty footprint `Modifies<{}, boolean>`.
// Under Node, calling `hasA("a")` twice returns `true` then `false`.
const globalRe = /a/g;

export function hasA(s: string): Modifies<{}, boolean> {
  return globalRe.test(s);
}
