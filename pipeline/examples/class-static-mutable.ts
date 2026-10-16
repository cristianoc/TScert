// A mutable static field is module state the class owns: outside the
// fragment.
class Counter {
  static count: number = 0;
}
export function read(): number {
  return Counter.count;
}
