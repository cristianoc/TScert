// An element of a `Uint8Array`, `Uint16Array` or `Int32Array` is a safe
// integer within its format's range (`%ByteAt%`'s bounded signature of each
// integer format), so its read is bound at `SafeInt` and used as an index
// with no `safeInteger(...)`.

/** @requires 0 <= i && i < bytes.length */
export function byteAt(bytes: Uint8Array, i: SafeInt): SafeInt {
  const k: SafeInt = bytes[i]!;
  return k;
}

/** @requires 0 <= i && i < words.length */
export function wordAt(words: Int32Array, i: SafeInt): SafeInt {
  return words[i]!;
}

/** @requires 0 <= i && i < codes.length && 256 <= table.length */
export function lookup(table: number[], codes: Uint8Array, i: SafeInt): number {
  return table[codes[i]!]!;
}
