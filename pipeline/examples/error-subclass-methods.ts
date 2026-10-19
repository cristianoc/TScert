// Methods of classes extending `Error`, on a direct subclass and one below
// it: each instance's prototype chain holds them past the message link
// (run under Node).
class Located extends Error {
  text(): string {
    return `at: ${this.message}`;
  }
}

class Coded extends Located {
  readonly code: number;
  constructor(code: number, message: string) {
    super(message);
    this.code = code;
  }
  more(): string {
    return `${this.text()} (${this.code})`;
  }
}

export function direct(): string {
  return new Located("x").text();
}

export function deeper(): string {
  return new Coded(2, "y").more() + new Located().text();
}
