// An override taking a narrower parameter than the method it overrides.
// TypeScript's method bivariance admits it, but a `Dog` would then not be an
// `Animal`: `a.feed(2)` would pass `2` where the override expects `1`.
class Animal {
  feed(amount: number): number {
    return amount;
  }
}
class Dog extends Animal {
  feed(amount: 1): number {
    return amount;
  }
}
export function main(): number {
  const a: Animal = new Dog();
  return a.feed(2);
}
