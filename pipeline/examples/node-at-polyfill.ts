// Under ES2021 the standard library declares no `at`; Node's declarations
// merge one into arrays and strings (`RelativeIndexable<T>`), the reviewed
// contract, which the host's prototypes hold: both reads are the reviewed
// `at`.
export function last(xs: readonly number[]): number | undefined {
  return xs.at(-1);
}
export function first(s: string): string | undefined {
  return s.at(0);
}
