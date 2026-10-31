// At `body` an open read admits an arm stating no `body` only of the host
// package: an arm of the program's own type stating no `body` may carry a
// getter there, which external code supplies at an unstated key and which
// runs code at each read, here counting its reads (run under Node). The
// read after the passed test stays refused (TypeScript narrows to
// `WithBody`).
interface WithBody {
  kind: "with";
  body: number | undefined;
}
interface WithoutBody {
  kind: "without";
}
export function bodyOf(d: WithBody | WithoutBody): unknown {
  return "body" in d ? d.body : undefined;
}
