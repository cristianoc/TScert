// A stated arrow popping the array it is handed where its flag is `true`:
// its statement is refused over its annotated domain, which admits `true`
// (a control claims it at a flag of `false` alone, where its code is within
// the empty footprint, and is refused for offering no row over the whole
// domain).
export const flagged = (
  xs: number[],
  flag: boolean,
): Within<{ value: "keep"; store: "keep" }, number> => {
  if (flag) xs.pop();
  return 0;
};
