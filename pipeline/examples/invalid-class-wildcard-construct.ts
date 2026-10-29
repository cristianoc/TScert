// A value typed `abstract new (...args: never) => Box` admits no argument
// list, an empty one included: constructing it with none is refused. Under
// Node, `made(Labelled)` returns a Box whose `label` is undefined where a
// string is promised.
interface Box {
  label: string;
}
class Labelled {
  label: string;
  constructor(label: string) {
    this.label = label;
  }
}
function made(c: abstract new (...args: never) => Box): Box {
  // @ts-expect-error: no argument list is a value of `never`, and `c` may be abstract
  return new c();
}
export function run(): string {
  return made(Labelled).label;
}
