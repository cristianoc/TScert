// A file's text as a compiler decodes its bytes: a UTF-16 byte order mark
// decodes the rest as UTF-16, a UTF-8 one is dropped, and other bytes are
// UTF-8, which they must be (run under Node: a malformed byte throws). The
// global `TextDecoder`, whose declared type is a conditional type, is read
// at its overlay entry: constructed, its `decode` taking a view of bytes.
export function decoded(bytes: Buffer): string {
  const utf16 = (encoding: string): string =>
    new TextDecoder(encoding).decode(
      bytes.subarray(2, 2 + ((bytes.length - 2) & ~1)),
    );
  if (bytes[0] === 0xff && bytes[1] === 0xfe) return utf16("utf-16le");
  if (bytes[0] === 0xfe && bytes[1] === 0xff) return utf16("utf-16be");
  const utf8 =
    bytes[0] === 0xef && bytes[1] === 0xbb && bytes[2] === 0xbf
      ? bytes.subarray(3)
      : bytes;
  return new TextDecoder("utf-8", { fatal: true }).decode(utf8);
}
