// A function declaration's binding is mutable in JavaScript. Reassigning it
// would change what every caller reaches, so it is outside the fragment.
function id(x: boolean): boolean {
  return x;
}
export function rebind(x: boolean): boolean {
  id = (y: boolean): boolean => !y;
  return id(x);
}
