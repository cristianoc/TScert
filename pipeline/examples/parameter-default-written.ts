// An annotated parameter with a default that the function assigns: the
// default binds a hidden name, then the source name is a `let` of its own
// initialized with its value, its contract the annotation. As
// array-prototype.mts#primitivePrototype assigns `entries`.
type Entry = { name: string; stated?: readonly string[] };
export function prototypeOf(kind: string, separators: readonly string[] = [],
    entries: readonly Entry[] = []): number {
  const owned = entries.find(e => kind === "string" && e.name === "length");
  if (owned) throw Error(`a string owns '${owned.name}'`);
  entries = entries.map(e => kind === "string" && e.name === "split" && e.stated
    ? { ...e, stated: [...separators, ...e.stated] } : e);
  return entries.length;
}

// A closure of a later default reads the binding the body writes.
export function later(a: number = 1, read: () => number = () => a): number {
  a = 2;
  return read();
}

// A defaulted parameter of a union narrowed, then written.
type Shape =
  | { kind: "circle"; radius: number }
  | { kind: "square"; side: number };
export function side(s: Shape = { kind: "square", side: 1 }): number {
  if (s.kind === "circle") return 0;
  s = { kind: "square", side: 2 };
  return s.side;
}

// A closure's defaulted parameter, written in its body.
export const closure = (s: string = "x"): string => {
  s += "!";
  return s;
};
