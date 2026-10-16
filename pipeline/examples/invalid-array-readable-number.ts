// Array.isArray gives unknown elements, including undefined at a hole.
// It establishes neither a numeric element contract nor physical density.
export function numeric(value: {}): readonly number[] {
  if (Array.isArray(value)) {
    return value;
  }
  return [];
}
