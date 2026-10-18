// A caught value is `unknown`, which `typeof` refines to an object that may be
// a host object: `Object.values` of it is refused (R8, COMPILER-API.md).
export function launder(f: () => void): unknown[] {
  try {
    f();
    return [];
  } catch (e) {
    if (typeof e === "object" && e !== null) return Object.values(e);
    return [];
  }
}
