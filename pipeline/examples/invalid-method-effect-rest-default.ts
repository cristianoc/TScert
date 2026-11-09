// A stated closure collecting a rest array whose default pops an array: the
// default runs as a node of the code checked at the annotation's own
// signature, statement included (run under Node: the default pops).
export const bad = (
  xs: number[],
  x: number = xs.pop() ?? 0,
  ...more: number[]
): Modifies<{}, number> => x + more.length;
