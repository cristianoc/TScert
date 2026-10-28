// A walk erasing a typed tree to `unknown` and finding its nodes by key
// name: a member read after `"k" in v`, an open read, and `Object.values`
// of an object of unknown type, which may be a host object. It stands for
// the walks `namesRead`, `namesArray`, `deferredIn`, `renamedModule` and
// `presentObligation`'s visit read as before their repair
// (SOURCE-REWRITES.md, "A typed tree walked as `unknown`").
function namesRead(e: unknown, out: Set<string>): Set<string> {
  if (Array.isArray(e)) e.forEach((x: unknown) => namesRead(x, out));
  else if (e !== null && typeof e === "object") {
    if ("k" in e && e.k === "id" && "name" in e && typeof e.name === "string") out.add(e.name);
    Object.values(e).forEach((v: unknown) => namesRead(v, out));
  }
  return out;
}
