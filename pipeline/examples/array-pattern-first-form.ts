// An array pattern binding the first element of an array: a list or a
// one-element literal chosen by `??`, and a fresh literal spreading two
// read-only arrays. Each position is the element or `undefined`.
// Census sites: declaration-graph.mts#selectGlobal's `const [first] = forms`,
// unchecked.mts#check's `const [first] = [...syntactic, ...semantic]`.
type Form = { binders: string[] };

export function firstForm(
  several: Form[] | undefined,
  stated: Form | undefined,
): Form | undefined {
  const forms = several ?? (stated === undefined ? undefined : [stated]);
  if (forms === undefined) return undefined;
  const [first] = forms;
  return first;
}

export function firstOfBoth(
  a: () => readonly string[],
  b: () => readonly string[],
): string | undefined {
  const [first] = [...a(), ...b()];
  return first;
}
