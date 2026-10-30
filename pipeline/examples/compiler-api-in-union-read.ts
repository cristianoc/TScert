// A node's `body` and `type` after `in` tests on unions of node kinds some
// of which state neither: every node inherits both getters, which read the
// kind's named child or `undefined`, so each read is the audited open read
// at `unknown` (C5 of tests/compiler-api.mts). A test makes the read
// eligible in each syntactic form; eligibility ignores a reassignment
// between the test and the read.
// Census functions: written-applications.mts#writtenApplications,
// host-families.mts#familyTable.
import type {
  SignatureDeclaration,
  TypeElement,
} from "typescript/unstable/ast";

export function signatures(
  functions: readonly SignatureDeclaration[],
): SignatureDeclaration[] {
  return functions.filter((d) => !("body" in d && d.body));
}
export function typed(signature: TypeElement): unknown {
  if (!("type" in signature) || !signature.type) return undefined;
  return signature.type;
}
export function either(d: SignatureDeclaration): unknown {
  return !("body" in d) || d.body;
}
export function choice(d: SignatureDeclaration): unknown {
  return "body" in d ? d.body : null;
}
export function branch(s: TypeElement): unknown {
  if ("type" in s) {
    return s.type;
  }
  return null;
}
export function reassigned(s: TypeElement, other: TypeElement): unknown {
  if ("type" in s) {
    s = other;
    return s.type;
  }
  return null;
}
