// The reserved writes' twins, each at its own key, which no object holds as a
// property the model does not state: a destructuring target, a compound and
// a logical assignment, a closure's write and a computed key, each lowered as
// a write. `pipeline/test.mts` renames one key at a time to `stack` in this
// run's documents: the reserved-write check alone refuses each.
export function pattern(o: { stackPattern: string }): string[] {
  [o.stackPattern] = ["s"];
  return Object.keys(o);
}

export function update(o: { stackUpdate: string }): string[] {
  o.stackUpdate += "s";
  return Object.keys(o);
}

export function logical(o: { stackLogical: string | null }): string[] {
  o.stackLogical ??= "s";
  return Object.keys(o);
}

export function callback(o: { stackCallback: string }): string[] {
  const set = (v: string): void => {
    o.stackCallback = v;
  };
  set("s");
  return Object.keys(o);
}

export function computed(
  o: { stackComputed: string },
  k: "stackComputed",
): string[] {
  o[k] = "s";
  return Object.keys(o);
}
