// A key two spreads give: the later spread's literal may give it, so the
// copy's key is either's (run under Node: `count(true)` is "s").
export function count(dots: boolean): number {
  const a = () => ({ k: 1 });
  const b = () => (dots ? { k: "s" } : {});
  const o = { ...a(), ...b() };
  return o.k;
}
