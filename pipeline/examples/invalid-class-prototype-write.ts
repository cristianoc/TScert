// A write to a class's `prototype` replaces a method every instance reads:
// the class value holds no `prototype` field, so the write is refused.
class Entry {
  isDirectory(): boolean {
    return false;
  }
}

export function replace(): void {
  Entry.prototype.isDirectory = () => true;
}

export function check(): boolean {
  return new Entry().isDirectory();
}
