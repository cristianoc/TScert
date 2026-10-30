// A function a record field holds, passed to map, where the field's type
// takes further actuals at a rest of strings: map passes the index, a
// number, there, and a function of the type reading a string's `length`
// of it returns `undefined` where a number is promised.
type Mapper = {
  num: (n: number, ...further: string[]) => Within<{ value: "any"; store: "grow" }, number>;
};
export function wrong(list: number[], m: Mapper): number[] {
  return list.map(m.num);
}
