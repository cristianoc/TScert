// A recursive constant calling its self entry at a longer signature, whose
// last invocation clears a tested field and throws: the closure changes the
// field on its exceptional edge, so after the caught call the field is read
// at its declared `string | undefined`, and the function returns
// `undefined` where a string is promised.
type Row = (n: number, extra: number) => void;
type Box = { v: string | undefined };

export function exceptional(o: Box): string {
  const f = (n: number): void => {
    const again: Row = f;
    if (n > 0) return again(n - 1, 0);
    o.v = undefined;
    throw "done";
  };
  if (o.v === undefined) return "";
  try {
    f(1);
  } catch {}
  return o.v;
}
