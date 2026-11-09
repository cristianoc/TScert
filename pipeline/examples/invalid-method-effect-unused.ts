// A stated arrow that pops the array it is handed, which no code of its
// module calls: its code is certified at its statement whether or not it is
// called, since another module reads the statement from its annotation.
export const bad = (xs: number[]): Modifies<{}, number> => {
  xs.pop();
  return 0;
};
