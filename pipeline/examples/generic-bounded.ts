function boundedPick(flag: boolean, other: boolean): boolean {
  const pick = <U, T extends U>(first: U, second: T): U => second;
  const kept = pick(flag, true);
  return kept ? pick(other, false) : other;
}
