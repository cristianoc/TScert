// A member named `message` would replace the message `Error` installs:
// refused at the member.
class Fixed extends Error {
  message: string = "fixed";
}
export function read(): string {
  return new Fixed("x").message;
}
