// A view of `length` at a type excluding a number admits no array: the read
// is at the object's own location. One at every number may be an array's,
// and the read tests the object, in a module stating no array type too.
export function label(x: { readonly length: string }): string {
  return x.length;
}

export function one(x: { readonly length: 1 }): 1 {
  return x.length;
}

export function count(x: { readonly length: number }): number {
  return x.length;
}

export function pattern(x: { readonly length: string }): string {
  const { length } = x;
  return length;
}

export function use(): number {
  return count({ length: 2 }) + one({ length: 1 });
}
