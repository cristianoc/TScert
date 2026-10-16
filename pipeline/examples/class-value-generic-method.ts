// A class value passed to a generic method, as a Mapper class is passed
// to EagerCollection.map: the method's binder is inferred from the class's
// instance, its pack from the further actuals, and its result is the
// interface itself, at the inferred binder.
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
class Show implements Mapper<number, string> {
  mapEntry(v: number): string {
    return "shown";
  }
}
class Scale implements Mapper<number, number> {
  constructor(factor: number) {}
  mapEntry(v: number): number {
    return v;
  }
}
export function show(b: Box<number>): Box<string> {
  return b.map(Show);
}
export function scale(b: Box<number>): Box<number> {
  return b.map(Scale, 2);
}
