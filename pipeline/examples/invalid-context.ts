function badFreshObject(seed: number): boolean {
  const cell: { value: boolean } = { value: seed };
  return cell.value;
}
