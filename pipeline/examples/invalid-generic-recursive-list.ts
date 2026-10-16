// A number is no `T`: a `List<T>` holding one is wrong at `T := string`.
type List<T> = null | { head: T; tail: List<T> };

function wrongHead<T>(xs: List<T>, n: number): List<T> {
  return { head: n, tail: xs };
}
