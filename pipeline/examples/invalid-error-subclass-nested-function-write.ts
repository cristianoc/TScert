// A function in a constructor binds its own `this`: its write of
// `this.message` is no field of the instance's allocation, so the parser
// leaves it to the reserved-write rule, which refuses it at the write: the
// receiver `{ message: string }` bounds no keys.
class Located extends Error {
  readonly note: { message: string };
  constructor(m: string) {
    super(m);
    const box = {
      message: "a",
      set: function (this: { message: string }, v: string): void {
        this.message = v;
      },
    };
    box.set("b");
    this.note = { message: box.message };
  }
}

export function note(): string {
  return new Located("x").note.message;
}
