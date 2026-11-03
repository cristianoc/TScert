// `item !== undefined || total > 10` holds where `item` is undefined and
// the total past 10: its cast in the body is refused (with `next` giving
// `"abcdefghijk"` once, then undefined, `wrong(next)` throws under Node).
export function wrong(next: () => string | undefined): number {
  let total = 0;
  let item = next();
  while (item !== undefined || total > 10) {
    total += (item as string).length;
    item = next();
    if (total < 2) continue;
  }
  return total;
}
