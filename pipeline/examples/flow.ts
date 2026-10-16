function branchRefinement(value: number | null): number {
  if (value !== null) {
    return value;
  } else {
    return 0;
  }
}
function conditionalRefinement(value: boolean | null): boolean {
  return value === null ? false : value;
}
function nullish(value: number | undefined): number {
  return value ?? 0;
}
