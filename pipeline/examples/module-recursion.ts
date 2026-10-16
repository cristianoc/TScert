// Function declarations are hoisted: a body may call itself, or a function
// declared after it.
function countdown(x: boolean): boolean {
  if (x) {
    return countdown(false);
  }
  return true;
}
function even(n: boolean): boolean {
  if (n) {
    return odd(false);
  }
  return true;
}
function odd(n: boolean): boolean {
  if (n) {
    return even(false);
  }
  return false;
}
