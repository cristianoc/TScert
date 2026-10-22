// A key written before a spread whose literal may give it: the copy's key is
// either's (run under Node: `label(true)` is 1).
export function label(dots: boolean): string {
  const o = { name: "x", ...(dots ? { name: 1 } : {}) };
  return o.name;
}
