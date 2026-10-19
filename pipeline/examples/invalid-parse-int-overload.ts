// Another module of the project adds `parseInt(value: boolean)`: a call
// resolving to it is to an overload no reviewed entry lists, refused rather
// than read at the augmentation's declaration (under Node, `NaN`).
export function fromFlag(flag: boolean): number {
  return parseInt(flag);
}
