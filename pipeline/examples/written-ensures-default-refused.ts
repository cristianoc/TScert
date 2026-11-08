/** @ensures result.length === source.length */
export function defaulted(source: string = ""): Uint8Array {
  return new Uint8Array(source.length);
}
