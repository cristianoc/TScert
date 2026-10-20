// Closure parameters TypeScript types from their context as function types:
// one the program writes, read as written (a guard's promise included), and
// a generic declaration's function type at an instance or a function's
// `typeof`, read through its one call signature at the instantiated types:
// an optional parameter with its `undefined`, a rest at its element, a
// guard's promise as a second form.
interface Scope {
  named(name: string, read: (text: string) => number): number;
  checked(value: unknown, test: (v: unknown) => v is string): string;
}

interface Box<T> {
  use(cb: (x: T, at?: number) => string): string;
  all(cb: (...xs: T[]) => number): number;
  test(cb: (v: unknown) => v is T): T | null;
}

function length(text: string): number {
  return text.length;
}

function isString(v: unknown): v is string {
  return typeof v === "string";
}

function count(...xs: string[]): number {
  return xs.length;
}

function useScope(scope: Scope): number {
  return scope.named("abc", length) + scope.checked(1, isString).length;
}

function useBox(box: Box<string>): string {
  return (
    box.use((x, at) => x.slice(at ?? 0)) +
    box.all(count) +
    (box.test(isString) ?? "")
  );
}

function measured(cb: (f: typeof length) => number): number {
  return cb(length);
}

export function run(): number {
  return useScope({
    named(name, read) {
      return read(name);
    },
    checked(value, test) {
      return test(value) ? value : "";
    },
  });
}

export function runBox(): string {
  return useBox({
    use(cb) {
      return cb("text", 1) + cb("text");
    },
    all(cb) {
      return cb("a", "b");
    },
    test(cb) {
      const v: unknown = "value";
      return cb(v) ? v : null;
    },
  });
}

export function runTypeof(): number {
  return measured((f) => f("abc"));
}
