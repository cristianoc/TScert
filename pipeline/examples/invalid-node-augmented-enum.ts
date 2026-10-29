// `argon2`, which an augmentation of `node:crypto`'s declarations states as
// an enum whose `tag` is 1 (`library-project/node-crypto-augmentation.d.ts`).
// Under Node, `argon2` is a function and `argon2.tag` is undefined, so
// `probe()`, declared `number`, returns undefined (run under Node). A Node
// module's enum, which no entry of the overlay reviews, is refused where it
// is imported.
import { argon2 } from "node:crypto";
export function probe(): number {
  return argon2.tag;
}
