// A fresh error's `name` is `Error.prototype`'s, not its own, and a message
// it was not given is the prototype's too: `new Error(m)` is stated as an
// object owning `message` only, so it is no `Error`, whose fields a record
// type says are its own.
function wrapped(): Error {
  return new Error("boom");
}
