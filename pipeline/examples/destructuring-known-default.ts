export function objectDefault(x: { f: number }): number {
  const { f = false } = x;
  return f;
}

export function nullDefault(x: { f: null }): null {
  const { f = 1 } = x;
  return f;
}

export function optionalDefault(x: { f?: number }): number | boolean {
  const { f = false } = x;
  return f;
}

export function unionDefault(
  x: { f: number } | { f: string },
): number | string {
  const { f = true } = x;
  return f;
}

export function tupleDefaults(
  xs: [number, string | undefined, boolean],
): number {
  const [first = false, , third = "fallback"] = xs;
  return first;
}

export function skippedEffect(
  x: { f: number },
  state: { value: number | null },
): number {
  state.value = 1;
  const { f = (state.value = null) } = x;
  return f;
}
