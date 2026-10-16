// JavaScript copies a `for` loop's `let` binding into each iteration, so each
// closure here captures its own `i`. The lowering binds `i` once for the whole
// loop, which differs exactly when a closure captures it: refused.
function captures(n: number): () => number {
  let last: () => number = () => 0;
  for (let i: number = 0; i < n; i = i + 1) {
    last = () => i;
  }
  return last;
}
