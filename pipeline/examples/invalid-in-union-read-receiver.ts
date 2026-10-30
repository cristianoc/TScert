// At `body` and `type` an open read admits an arm stating no key only of
// the host package, its bases included: an arm of the standard library's
// `Error`, of a program interface extending it, or `object`, may carry a
// getter at the key, which an external subclass's prototype can hold, so
// each read stays refused.
interface Typed {
  type: string | undefined;
}
interface LocalError extends Error {}
export function library(d: Error | Typed): unknown {
  return "type" in d ? d.type : undefined;
}
export function local(d: LocalError | Typed): unknown {
  return "type" in d ? d.type : undefined;
}
export function plain(o: object): unknown {
  return "body" in o ? o.body : undefined;
}
