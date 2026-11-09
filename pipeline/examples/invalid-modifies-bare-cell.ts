// A bare key naming a module binding: a module cell is written
// `"cell(scriptClasses)"`, so the reader refuses the bare key.
let scriptClasses: number[] | null = null;

export function classes(): Modifies<
  { values: "any"; scriptClasses: "init" },
  number[]
> {
  scriptClasses ??= [];
  return scriptClasses;
}
