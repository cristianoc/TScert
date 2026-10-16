// A spread of a function copies its own enumerable properties: the fields its
// type states, and whatever else was assigned to it, which the copy's type
// leaves open. A function the program creates owns none.
export function copy(f: () => number): object {
  return { ...f };
}

export function tagged(f: (() => number) & { tag: string }): { tag: string } {
  return { ...f };
}

export function rest(
  f: (() => number) & { tag: string; read: () => number },
): number {
  const { tag, ...others } = f;
  return others.read() + tag.length;
}

export function created(): { label: string } {
  const counter = Object.assign((n: number) => n + 1, { label: "count" });
  return { ...counter };
}
