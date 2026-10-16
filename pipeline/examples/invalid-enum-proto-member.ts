// TypeScript's emit writes each enum member by assignment: `P["__proto__"] =
// 1` runs the prototype's setter, which ignores a number and creates no
// property, so `P.__proto__`, typed 1, reads Object.prototype. A member named
// __proto__ is refused.
enum P {
  "__proto__" = 1,
}
function proto(): 1 {
  return P.__proto__;
}
