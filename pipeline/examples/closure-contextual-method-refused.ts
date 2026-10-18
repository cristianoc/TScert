// A contextual closure parameter at an object literal's type with a method:
// read member by member, a method is no field an object contract states,
// so the parameter is refused at the source.
export function calls(): number[] {
  const xs = [
    {
      f(): number {
        return 1;
      },
    },
  ];
  return xs.map((x) => x.f());
}
