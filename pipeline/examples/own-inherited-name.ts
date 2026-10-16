// A field the type requires is the object's own, whatever its name: a read
// of a required `toString` finds it, not `Object.prototype`'s member.
export function own(d: {
  readonly [k: string]: number;
  readonly toString: number;
}): number {
  return d.toString;
}

export function make(): number {
  return own({ toString: 3 });
}
