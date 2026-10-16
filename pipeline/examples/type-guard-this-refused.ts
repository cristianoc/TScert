// A guard about the receiver: its promise is about `this`, which no
// promise signature's parameters index.
export class Node {
  constructor(readonly name: string | null) {}
  isNamed(): this is { name: string } {
    return this.name !== null;
  }
}
