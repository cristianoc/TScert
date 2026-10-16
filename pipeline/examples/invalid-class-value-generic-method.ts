interface Mapper<V1, V2> {
  mapEntry(v: V1): V2;
}
interface Box<V> {
  get(): V;
  map<V2, P extends readonly number[]>(
    m: new (...p: P) => Mapper<V, V2>,
    ...p: P
  ): Box<V2>;
}
// A mapper of strings: a Box of numbers would call it with a number.
class Shout implements Mapper<string, string> {
  mapEntry(v: string): string {
    return v;
  }
}
export function shout(b: Box<number>): Box<string> {
  return b.map(Shout);
}
