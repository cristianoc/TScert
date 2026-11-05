// An optional visitor declared as a method is compared bivariantly, so
// TypeScript accepts a closure whose one parameter is narrower than the
// visitor's first. The walker passes `undefined` there, and the closure's
// `toFixed` throws a TypeError: the closure is offered no signature its
// parameter does not take, and the call meets no claim of it.
interface Visitor {
  line?(width: number | undefined, start: number, end: number): void;
}

function walk(widths: number[], visitor: Visitor): number {
  let lines = 0;
  for (let i = 0; i < widths.length; i++) {
    visitor.line?.(i === 0 ? undefined : widths[i], i, i + 1);
    lines++;
  }
  return lines;
}

export function digits(widths: number[]): number {
  let total = 0;
  walk(widths, {
    line: (width: number) => {
      total += width.toFixed().length;
    },
  });
  return total;
}
