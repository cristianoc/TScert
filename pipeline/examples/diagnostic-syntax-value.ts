// An opaque child supplies unknown instead of inventing an empty field type.
export function syntaxValue(): string {
  return import.meta.dirname;
}
