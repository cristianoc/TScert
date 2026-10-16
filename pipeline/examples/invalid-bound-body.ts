function reversedBody(flag: boolean, other: boolean): boolean {
  const pick = <U, T extends U>(first: U, second: T): T => first;
  const kept = pick(flag, other);
  return kept ? pick(other, flag) : other;
}
