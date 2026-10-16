// An imported unique symbol is the one symbol its declaration names: a binding
// annotated with `typeof` it holds that symbol.
import { brand } from "@fixture/lib";

const held: typeof brand = brand;

export function same(): boolean {
  return held === brand;
}
