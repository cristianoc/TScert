// `keyof` of a record is the union of its keys, not one of them.
export function bad(k: keyof { a: number; b: string }): "a" {
  return k;
}
