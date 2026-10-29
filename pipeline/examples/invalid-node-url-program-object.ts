// `fileURLToPath` tests a URL by reading its `href` and `protocol`, and
// then decodes its `pathname` by `decodeURIComponent`, which converts a
// program's object by its `toString` (run under Node: `answer` runs, and
// its answer is the path). No program object meets `URL`, a host object's
// type, refused.
import { fileURLToPath } from "node:url";

export function pathOf(answer: () => string): string {
  const pathname = { length: 0, toString: answer };
  const url = {
    href: "file:///x",
    protocol: "file:",
    hostname: "",
    pathname,
  } as URL;
  return fileURLToPath(url);
}
