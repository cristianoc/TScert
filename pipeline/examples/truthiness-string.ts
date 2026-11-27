// A falsy string narrows to the singleton `""`.
function falsyString(s: string): "" {
  if (!s) {
    return s;
  }
  return "";
}
