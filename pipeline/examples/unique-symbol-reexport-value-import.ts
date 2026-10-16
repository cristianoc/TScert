// A unique symbol re-exported under another name is the symbol it
// re-exports: the alias and the original share one identity.
import { brand } from "@fixture/lib";
import { relayedBrand } from "@fixture/relay";

const held: typeof brand = relayedBrand;

export function same(): boolean {
  return held === brand;
}
