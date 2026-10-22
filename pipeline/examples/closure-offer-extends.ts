// A closure over a base interface passed to `forEach` and `map` over an
// array of an interface extending it: each element is within the closure's
// parameter by width (`Labelled` holds `size` beside `label`) and depth
// (`kind` a literal within `string`), so the callback's signature at the
// element is offered to the closure (SOURCE-ELABORATION.md, "Source
// closures and their annotations").
interface Base {
  readonly kind: string;
  readonly label: string;
}
interface Labelled extends Base {
  readonly kind: "labelled";
  readonly size: number;
}

export function labels(xs: Labelled[]): string[] {
  const out: string[] = [];
  const one = (b: Base): void => {
    out.push(b.label);
  };
  xs.forEach(one);
  return out;
}

export function kinds(xs: readonly Labelled[]): string[] {
  const kind = (b: Base): string => b.kind;
  return xs.map(kind);
}
