// A predicate of the sync API the contract states no promise for is read
// without it (HOST-FAMILIES.md, "Guard recognition"; COMPILER-API.md, "Stated
// type guards"), `isIntrinsicType` among them: the `true` edge does not
// narrow `type` to an intrinsic type, which alone states `intrinsicName`.
import { isIntrinsicType, type Type } from "typescript/unstable/sync";

export function name(type: Type): string | undefined {
  return isIntrinsicType(type) ? type.intrinsicName : undefined;
}
