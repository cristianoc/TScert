// A callback constructing a class whose constructor pops the array being
// mapped: the class's construct signature states the ordinary effect, so
// `map` takes its unrestricted overload and the result is sparse. The pop
// shows: the result has a hole below its length.
class Shrink {
  size: number;
  constructor(xs: number[]) {
    xs.pop();
    this.size = xs.length;
  }
}

export function shrinkAll(xs: number[]): number[] {
  return xs.map((x: number): number => new Shrink(xs).size + x);
}
