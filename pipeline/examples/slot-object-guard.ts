// An assigned parameter holding an object beside `null`, a slot of its
// activation: a guard finding an object narrows it, and the read through it
// is at the object.
type List = null | { head: number; tail: List };
export function length(l: List): number {
  let n = 0;
  while (l !== null) {
    n = n + 1;
    l = l.tail;
  }
  return n;
}
