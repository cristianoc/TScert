// A class's method replaced through `Reflect.set` by a function returning a
// number (run under Node: the `boolean` call returns 7): `Reflect` is
// outside the reviewed globals, refused where it is read.
class Entry {
  isDirectory(): boolean {
    return false;
  }
}

export function replace(): void {
  Reflect.set(Entry.prototype, "isDirectory", () => 7);
}

export function check(): boolean {
  return new Entry().isDirectory();
}
