// Object literal keys: a number names the property its ToString spells, in a
// literal and in a type alike; a spread of an object literal is its fields,
// evaluated where written.
function numbered(): { 0: number; 1.5: string } {
  return { 0: 1, 1.5: "a" };
}
function read(o: { 0: number }): number {
  return o[0];
}
function siblings(): { s: string; n: number; q: boolean } {
  return { s: "a", n: 1, ...{ q: true } };
}
