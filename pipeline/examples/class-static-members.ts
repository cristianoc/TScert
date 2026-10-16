// A class's static fields are initialized in order, an initializer reading
// an earlier one, and are own data properties of the class value, which
// `C.x` reads where TypeScript binds it to the member; its static methods
// are bindings of their own, whose calls pass no receiver they read, so they
// may be detached or passed as callbacks. A parameter named like the class
// is not it.
function defaultPort(): number {
  return 8080;
}
class Config {
  static readonly port: number = defaultPort();
  static readonly next: number = Config.port + 1;
  static make(): Config {
    return new Config();
  }
  value: number = 1;
  read(): number {
    return this.value;
  }
}
function callsCb(cb: () => Config): number {
  return cb().value;
}
export function use(): number {
  const make = Config.make;
  const typed: () => Config = Config.make;
  const port: number = Config.port;
  return (
    Config.make().read() +
    make().value +
    typed().value +
    callsCb(Config.make) +
    port +
    Config.next
  );
}
export function shadow(Config: { port: number }): number {
  return Config.port;
}
