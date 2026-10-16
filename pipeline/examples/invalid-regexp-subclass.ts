// A subclass's `exec` is what `replace` calls on its instances, and may build
// results the shape does not describe; a library class is no base.
class Fake extends RegExp {
  exec(s: string): RegExpExecArray | null {
    return null;
  }
}

export function make(): string {
  return "ab".replace(new Fake("(a)(b)"), "x");
}
