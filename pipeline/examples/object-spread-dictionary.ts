// A spread of a dictionary gives a dictionary: every key its index's class
// admits holds what either side gives there, so the result states the index,
// writable, at the union of both sides' index and field types.
export function view(a: { readonly [k: string]: number }): {
  readonly [k: string]: number;
} {
  return { ...a, x: 1 };
}

export function cell(a: { [k: string]: number }): { [k: string]: number } {
  const d: { [k: string]: number } = { ...a, x: 1 };
  return d;
}

export function two(
  a: { readonly [k: string]: number },
  b: { readonly [k: string]: string },
): { [k: string]: string | number } {
  return { ...a, ...b };
}

// A key the dictionary may hold is optional in the result, at either
// side's type.
export function thenOptional(): { a?: string | number } {
  const obj1: { [k: string]: number } = {};
  const obj2: { a?: string } = {};
  return { ...obj1, ...obj2 };
}

// The string and the symbol keys are apart, each index at its own type.
type Entries = { [k: string]: number; [k: symbol]: unknown };
export function both(a: Entries): Entries {
  const copy: Entries = { ...a };
  return copy;
}

// A key added to a local's own dictionary: its copy keeps the index.
export function grow(): { [k: string]: number } {
  const d: { [k: string]: number } = {};
  d.x = 5;
  d["y"] = 6;
  return d;
}
