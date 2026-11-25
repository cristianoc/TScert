// Multiple locally allocated arrays mutated by `.push()` and element writes
// inside a loop, then returned and stored on fields after the loop, leave
// quantified invariants on parameter objects outside the confined set intact.
/**
 * @invariant forall i in this.data.chunks: this.data.chunks[i] === null || 1 <= this.data.chunks[i].length
 * @invariant this.data.extras === null || forall i in this.data.chunks: this.data.chunks[i] === null || this.data.extras[i] === null || this.data.chunks[i].length <= this.data.extras[i].length
 */
type Holder = {
  data: {
    chunks: (number[] | null)[];
    extras: (number[] | null)[] | null;
  };
  starts: number[] | null;
  ends: number[] | null;
  marks: number[] | null;
};

export function buildSummaries(h: Holder): { starts: number[]; ends: number[]; marks: number[] } {
  const { chunks } = h.data;
  const starts: number[] = [];
  const ends: number[] = [];
  const marks: number[] = [];
  for (let i = 0; i < chunks.length; i++) {
    const c = chunks[i];
    starts.push(c === null ? 0 : c.length);
    ends.push(i);
    if ((i & 0x7fffffff) !== i || i > marks.length) throw new RangeError("index");
    marks[i] = c === null ? 0 : 1;
  }
  const out = { starts, ends, marks };
  h.starts = starts;
  h.ends = ends;
  h.marks = marks;
  return out;
}
