// `Error(m)` called without `new` runs the error constructor's steps: it is
// read as `new Error(m)`, a fresh error owning `message`, beside a
// construct of the same global.
function called(): string {
  const e = Error("boom");
  return e.message;
}

function both(flag: boolean): string {
  return (flag ? new Error("a") : Error("b")).message;
}

function fail(m: string): never {
  throw Error(m);
}
