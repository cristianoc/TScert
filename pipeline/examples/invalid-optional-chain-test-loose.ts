// `o?.v == null` holds where `o` is nullish: its true branch keeps `o`
// possibly undefined.
type Opt = { v?: string | null };

export function wrong(o: Opt | undefined): Opt {
  // @ts-expect-error o is undefined where the chain is
  if (o?.v == null) return o;
  return o;
}
