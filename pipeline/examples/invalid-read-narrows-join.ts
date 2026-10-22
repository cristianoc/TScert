// The first element saves d. The second and the remaining continuation
// both branch; the second may rebind d before the plain member read.
// wrong([{}], true, true) returns undefined.

type Declaration = { kind?: string; initializer?: string };

export function wrong(list: readonly Declaration[], write: boolean, read: boolean): Declaration {
  let d = list[0];
  const k = [d, write ? (d = list[1]) : d, read ? list[0].kind : 0];
  return d;
}
