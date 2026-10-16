function fabricatedPolymorphicResult(seed: boolean): boolean {
  const fabricate = <T>(value: T): T => true;
  return fabricate(seed);
}
