type A0 = { readonly k: "a"; readonly tag: "zero"; readonly value: number };
type A1 = { readonly k: "a"; readonly tag: "one"; readonly value: number };
type B = { readonly k: "a" };

export function competing(p: A0 | A1): number {
  const q: B = p;
  if (q.k === "a") return p.value;
  return 0;
}
