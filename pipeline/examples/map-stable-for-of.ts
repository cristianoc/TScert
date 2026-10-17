// A `map` callback looping over an array with `for...of`: the array
// iterator's step writes only its own position, a number, and the loop's
// body pushes onto an array the callback builds: the callback is within
// `{value: any, store: grow}`, which keeps every dense prefix, so the result
// is dense.
export function doubled(xss: readonly (readonly number[])[]): number[][] {
  return xss.map((xs: readonly number[]): number[] => {
    const out: number[] = [];
    for (const x of xs) out.push(x * 2);
    return out;
  });
}

// Global regex replacements in a declaration `map` calls: each writes only
// its regex's `lastIndex`.
const inlineMath = /\$`([^`]*)`\$/g;
function prose(text: string): string {
  return text
    .replace(/```math\n[\s\S]*?```/g, "")
    .replace(inlineMath, " ")
    .replace(/`[^`\n]*`/g, " ");
}
export function proses(texts: readonly string[]): string[] {
  return texts.map((t) => prose(t));
}
