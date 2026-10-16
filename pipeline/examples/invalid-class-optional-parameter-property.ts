// An optional parameter property holds the `undefined` an omitted argument
// binds: it is not a string.
class Tagged {
  constructor(public tag?: string) {}
}
export function tagOf(): string {
  const tag: string = new Tagged().tag;
  return tag;
}
