// The sync API's stated type guards (T7, COMPILER-API.md, "Stated type
// guards"): each call's `true` edge narrows its argument to the promised
// interface, whose members the front end reads: a union's or an
// intersection's `getTypes`, a literal type's `value`, a reference's
// `getTarget`. Both signatures are at the empty footprint.
import {
  TypeFlags,
  isBigIntLiteralType,
  isBooleanLiteralType,
  isIntersectionType,
  isNumberLiteralType,
  isStringLiteralType,
  isTypeReference,
  isUnionType,
  type Type,
} from "typescript/unstable/sync";

export function parts(type: Type): readonly Type[] {
  return isUnionType(type) || isIntersectionType(type)
    ? type.getTypes()
    : [type];
}

export function literal(
  type: Type,
): string | number | bigint | boolean | undefined {
  if (isStringLiteralType(type)) return type.value;
  if (isNumberLiteralType(type)) return type.value;
  if (isBigIntLiteralType(type)) return type.value;
  if (isBooleanLiteralType(type)) return type.value;
  return undefined;
}

export function target(type: Type): Type {
  return isTypeReference(type) ? type.getTarget() : type;
}

export function hasUndefined(type: Type): boolean {
  return (
    isUnionType(type) &&
    type.getTypes().some((t) => (t.flags & TypeFlags.Undefined) !== 0)
  );
}

// The empty footprint keeps what the caller knew of a field before the call.
export function kept(type: Type, box: { v: number | undefined }): number {
  if (box.v === undefined) return 0;
  return isUnionType(type) ? box.v : 1;
}
