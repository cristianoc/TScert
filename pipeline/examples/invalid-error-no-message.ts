// `new Error()` owns no `message`: reading one reads the prototype's. The
// overlay states the constructor at a string message only.
function empty(): string {
  const e = new Error();
  return e.message;
}
