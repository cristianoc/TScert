// The package's `./extra` export: a function of its own, and the `.`
// export's `prepare` again under another name.
import { twice } from "./internal";
export { prepare as make } from "./main";

export function doubled(n: number): number {
  return twice(n);
}
