// A falsy string is `""`, but `string` has no falsy singleton to narrow to.
function falsyString(s: string): "" {
  if (!s) {
    return s;
  }
  return "";
}
