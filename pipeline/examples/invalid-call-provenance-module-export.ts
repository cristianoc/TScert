// An exported function is held by every module importing it, which may give
// it an own `call` property before `probe` runs `g.call`.
export function g(): number {
  return 1;
}

export function probe(): number {
  return g.call(undefined);
}
