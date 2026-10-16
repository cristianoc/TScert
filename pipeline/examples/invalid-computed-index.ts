// A member type read by an indexed access is that member's declared type.
type Row = { meta: { tag: string } };
export function bad(r: Row): Row["meta"]["tag"] | number {
  return r.meta;
}
