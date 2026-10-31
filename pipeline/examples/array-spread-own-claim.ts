// Census functions: unchecked.mts#unstated, unchecked.mts#boundary.
export function appendResult(missing: string[], result: boolean): string[] {
  return result ? [...missing, "result"] : missing;
}

export function conditionalSpreads(
  missing: string[],
  result: boolean,
  moduleLevel: boolean,
): string[] {
  return [...(result ? ["its type"] : []), ...(moduleLevel ? missing : [])];
}
