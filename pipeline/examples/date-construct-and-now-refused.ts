// A global both constructed and read through its members is a class with
// members, which has no clause: `new Date()` beside `Date.now()`.
function both(): number {
  return new Date().getTime() - Date.now();
}
