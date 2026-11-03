// A call record whose discriminant a flag selects, built at the arm the flag
// selects: one record literal per arm, each with its conditional spreads.
// Census functions:
// fragment-expressions.mts#chainLink, fragment-expressions.mts#expr.
type E =
  | { k: "id"; name: string }
  | { k: "apply"; callee: E; args: E[]; spreads?: number[]; typeArgs?: string[] }
  | { k: "invoke"; callee: E; args: E[]; spreads?: number[]; typeArgs?: string[] };
export function call(method: boolean, callee: E, args: E[], spreads: number[], typeArgs: string[] | undefined): E {
  if (method)
    return {
      k: "invoke",
      callee,
      args,
      ...(spreads.length ? { spreads } : {}),
      ...(typeArgs?.length ? { typeArgs } : {}),
    };
  return { k: "apply", callee, args, ...(spreads.length ? { spreads } : {}) };
}
