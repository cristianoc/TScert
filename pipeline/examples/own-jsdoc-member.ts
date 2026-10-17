// A member named `jsDoc` of the file's own object is an ordinary field: only
// the host member TypeScript binds a read to is refused as allocating.
const page = { jsDoc: "summary" };

export function summary(): string {
  return page.jsDoc;
}
