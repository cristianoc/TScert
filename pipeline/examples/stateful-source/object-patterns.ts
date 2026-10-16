// An object pattern on a `const`: the initializer is evaluated once, each
// property is read in pattern order, and a default is evaluated only when
// that read is undefined. Every binding is an immutable local; the statement
// is one entry, and the entry after it states each binding's type.
function defaultedField(seed: number | undefined): number {
  const box = { value: seed };
  const { value = 0 } = box;
  return value;
}

// Without a default the binding is the read, at the field's own type.
function plainField(seed: number): number {
  const box = { value: seed };
  const { value } = box;
  return value;
}

// Defaults run in pattern order, each only on its own undefined read, so the
// later effect wins when both fields are undefined and neither runs when the
// fields are present. A property may bind under another name.
function orderedDefaults(seed: number | undefined): number {
  let state: number | null = null;
  const box = { a: seed, b: seed };
  const { a: first = (state = 1), b = (state = 2) } = box;
  return state ?? b;
}

// The binding copies the field's value: a later write to the field does not
// reach it.
function snapshotSurvivesWrite(seed: number): number {
  const box = { value: seed };
  const { value } = box;
  box.value = 0;
  return value;
}
