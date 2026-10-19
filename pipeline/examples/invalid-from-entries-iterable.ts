// `Object.fromEntries` of a program's iterable steps its iterator, code of
// the client's (run under Node: the iterator runs): stated at an array of
// pairs alone.
export function build(pairs: Iterable<readonly [string, number]>): {
  [k: string]: number;
} {
  return Object.fromEntries(pairs);
}
