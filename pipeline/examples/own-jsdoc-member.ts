// A member named `jsDoc` of the file's own object is an ordinary field, in
// every form that reads it: only the host member TypeScript binds a read to
// is refused as allocating.
type Page = { readonly jsDoc: string };
const page: Page = { jsDoc: "summary" };

export function summary(): string {
  return page.jsDoc;
}

export function element(): string {
  return page["jsDoc"];
}

export function bound(): string {
  const { jsDoc } = page;
  return jsDoc;
}

export function optional(p: Page | undefined): string {
  return p?.jsDoc ?? "";
}
