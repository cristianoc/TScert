// A `RegExp` annotation is a native regex: an object of the program's that
// states the members is none, so passing one where a `RegExp` is expected is
// refused. Its `exec` answers what it likes, here a number where a match's
// string is read.
type Matcher = { exec(s: string): unknown; test(s: string): boolean };

function first(re: RegExp, s: string): string {
  const m = re.exec(s);
  return m === null ? "" : m[0];
}

export function run(m: Matcher, s: string): string {
  return first(m as RegExp, s);
}
