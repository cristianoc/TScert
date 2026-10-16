// String members that throw on some arguments, read as declared (`repeat`
// of a negative count, `normalize` of an unknown form: `RangeError`s), and
// those whose declarations admit a `RegExp`, stated at a string pattern
// (`split`, `replace`, `replaceAll`); `toLocaleString` takes locales as a
// tag or a readonly array of tags.
function strings(s: string, n: number): string {
  const parts: string[] = s.split(",");
  const two = s.split(",", 2);
  const r = s.repeat(n) + s.normalize() + s.normalize("NFC");
  return (
    r +
    s.replace("a", "b") +
    s.replaceAll("a", "$&$&") +
    parts.length +
    two.length
  );
}

function locale(n: number, b: bigint): string {
  const tags: readonly string[] = ["en", "de"];
  return (
    n.toLocaleString() +
    n.toLocaleString("en-US") +
    n.toLocaleString(tags) +
    b.toLocaleString("de")
  );
}
