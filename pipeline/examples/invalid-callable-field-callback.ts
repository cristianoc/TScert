// A function a record field holds, passed to map, where the field's type
// states one parameter: a function of the type may take a further optional
// parameter, which map's index fills, returning `undefined` where a number
// is promised.
type Mapper = {
  num: (n: number) => Within<{ value: "any"; store: "grow" }, number>;
};
export function wrong(list: number[], m: Mapper): number[] {
  return list.map(m.num);
}
