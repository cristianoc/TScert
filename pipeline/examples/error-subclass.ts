// Classes extending the standard `Error`: each construction installs the
// instance's message, `""` where the message is omitted, beside the class's
// prototype, so a further subclass keeps it.
class Decline extends Error {}

export function decode(raw: string): string {
  try {
    if (raw.includes("\\")) throw new Decline("an escape");
    return raw;
  } catch (e) {
    if (e instanceof Decline) return "declined";
    throw e;
  }
}

type Span = [number, number];

export class DeclarationError extends Error {
  readonly at: Span;
  constructor(at: Span, message: string) {
    super(message);
    this.at = at;
  }
}

class Deeper extends DeclarationError {}

export function located(at: Span): DeclarationError {
  return new DeclarationError(at, "here");
}

export function deeper(): string {
  const e = new Deeper([0, 1], "deep");
  return `${e.message}@${e.at[0]}`;
}

export function omitted(): string {
  return new Decline().message;
}

export function described(e: Decline): string {
  const { message } = e;
  return message;
}

export function observed(): string {
  const e = new Deeper([2, 3], "kept");
  return `${Object.keys(e).join("|")},${e instanceof Error},${e instanceof DeclarationError}`;
}
