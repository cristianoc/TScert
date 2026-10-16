// In each iteration the write precedes the closure, but the second
// iteration's write follows the first iteration's closure: `f()` returns
// undefined after `loopCapture(2)`. The binding is a cell.
export function loopCapture(n: number): () => string {
  let x: string | undefined = "a";
  let f: () => string = () => "b";
  for (let i = 0; i < n; i++) {
    x = i === 0 ? "a" : undefined;
    if (i === 0) {
      f = (() => x) as () => string;
    }
  }
  return f;
}
