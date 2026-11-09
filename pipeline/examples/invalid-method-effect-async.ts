// A statement on an async method: an async call returns its promise where
// its body throws, so no footprint of its body's normal return is the
// call's.
export class Runner {
  async run(xs: number[]): Modifies<{}, Promise<number>> {
    return xs.length;
  }
}
