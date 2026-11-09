// A declaration stating the empty footprint whose parameter default pops an
// array: the default runs as a node of the declaration's graph, so its
// check at the statement covers it (run under Node: the default pops).
export function bad(
  xs: number[],
  x: number = xs.pop() ?? 0,
): Modifies<{}, number> {
  return x;
}
