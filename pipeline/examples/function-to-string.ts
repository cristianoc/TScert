// A function's `toString` is `Function.prototype`'s: on a parameter typed
// by its signature, on a class value, and on a callable or a string, each
// shape read through its own prototype.
export class Plain {
  static make(): Plain {
    return new Plain();
  }
}

export function ofArrow(f: (x: number) => number): string {
  return f.toString();
}

export function ofClass(): string {
  return Plain.toString();
}

export function ofEither(v: string | (() => void)): string {
  return v.toString();
}
