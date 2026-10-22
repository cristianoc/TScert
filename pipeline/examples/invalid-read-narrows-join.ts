// The second element may rebind d, and the third branches to a member read:
// past the expression d may be the undefined the second element wrote.
// wrong([{}], true, true) returns undefined.

type Declaration = { kind?: string; initializer?: string };

export function wrong(list: readonly Declaration[], write: boolean, read: boolean): Declaration {
  let d = list[0];
  const k = [d, write ? (d = list[1]) : d, read ? list[0].kind : 0];
  return d;
}
