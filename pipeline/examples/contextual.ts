function objectContract(seed: boolean): boolean | null {
  const box: { value: boolean | null } = { value: seed };
  box.value = null;
  return box.value;
}
function tupleContract(seed: number): string {
  const pair: [number, string] = [seed, "name"];
  return pair[1];
}
