// An augmentation of `node:crypto`'s declarations stating an enum `argon2`
// with a member `tag`. Under Node, `argon2` is a function, whose `tag` is
// undefined (invalid-node-augmented-enum).
import "node:crypto";
declare module "node:crypto" {
  enum argon2 {
    tag = 1,
  }
}
