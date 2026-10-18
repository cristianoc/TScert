// An exported module `let` is a live binding an importer reads: outside the
// fragment.
let shared: number = 0;
export { shared };

export function set(n: number): void {
  shared = n;
}
