// An interface merged from declarations binding different numbers of type
// parameters: each binds a prefix of the longest list, by position, and its
// members are read with only those. In the second declaration `T` is not a
// parameter: it names the alias `T`, a string, whatever the box's `T` is.
type T = string;

interface Box<A, T = number> {
  first: A;
  second: T;
}
interface Box<A> {
  label: T;
  again: A;
}

export function label(box: Box<boolean, number>): string {
  return box.label;
}

export function second(box: Box<boolean>): number {
  return box.second;
}

export function make(flag: boolean): Box<boolean, bigint> {
  return { first: flag, second: 1n, label: "box", again: !flag };
}
