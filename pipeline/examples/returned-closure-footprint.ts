// pretext's `lazyRegExp`: a factory returns a closure building its regular
// expression once, cached in a captured binding. The factory's claim states
// the returned closure's footprint, which its unit's return establishes, so
// a call of a closure it returned, held by a module constant or by an
// element of a module array, keeps the facts a call at that footprint
// keeps: the loop's reads below its bound after the calls are bounded.

export function lazyRegExp(source: string, flags: string): () => RegExp {
  let built: RegExp | null = null;
  return () => built ??= new RegExp(source, flags);
}

const letter = lazyRegExp("^\\p{L}$", "u");
const TESTS = [lazyRegExp("^\\p{M}$", "u"), lazyRegExp("^\\p{N}$", "u")];

let marked: number = 0;

/** Counts a text having the property: within `{value: any, store: keep}`. */
export function mark(text: string, property: number): void {
  if ((TESTS[property] ?? letter)().test(text)) marked += 1;
}

export function countLetters(texts: string[]): number {
  let count = 0;
  for (let i = 0; i < texts.length; i++) {
    const re = letter();
    if (re.test(texts[i]!)) count += 1;
    mark(texts[i]!, 1);
    count += texts[i]!.length;
  }
  return count + marked;
}
