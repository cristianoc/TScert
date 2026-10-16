// `for (const k in o)` visits keys, each a string, of any value.
function keys(o: { a: number; b: string }): number {
  let count: number = 0;
  for (const k in o) {
    const key: string = k;
    count = count + 1;
  }
  return count;
}

function ofAnything(x: unknown): boolean {
  let any: boolean = false;
  for (const k in x) {
    any = true;
  }
  return any;
}

function early(o: { [k: string]: number }): string | null {
  for (const k in o) {
    return k;
  }
  return null;
}
