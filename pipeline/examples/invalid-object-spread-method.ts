// A class instance's method is its prototype's, which a spread does not
// copy: the copy has no `read`. TypeScript drops it too, but accepts this
// annotation of the copy by the instance's structural type.
class Reader {
  value: number = 1;
  read(): number {
    return this.value;
  }
}
function copy(source: Reader): { value: number; read: () => number } {
  return { ...source };
}
export function main(): number {
  return copy(new Reader()).read();
}
