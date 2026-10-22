// A saved negation describes the tested value before the parameter write.
export function wrong(k: { name: "a" | "b" }, n: number): 1 {
  const ok = !(k.name !== "b" || n !== 1);
  n = 2;
  // @ts-expect-error n is not 1 after the write.
  if (ok) return n;
  return 1;
}
