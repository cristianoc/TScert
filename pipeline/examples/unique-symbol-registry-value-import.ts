// Two imported constants made by `Symbol.for` of one string hold one symbol,
// the registry's for that string: a value of `typeof sharedLeft` is
// `sharedRight`, though TypeScript types them distinct unique symbols.
import { sharedLeft, sharedRight } from "@fixture/lib";

const held: typeof sharedLeft = sharedRight;

export function same(): boolean {
  return held === sharedLeft;
}
