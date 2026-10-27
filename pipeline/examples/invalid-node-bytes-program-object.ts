// A program's object meeting a view's members is no view: `TextDecoder`'s
// `decode` throws on it (run under Node: a TypeError). No program object
// meets `Uint8Array`, a host object's type, refused.
export function decoded(): string {
  const bytes: Uint8Array = { length: 0 } as Uint8Array;
  return new TextDecoder().decode(bytes);
}
