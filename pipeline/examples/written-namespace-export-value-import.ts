// A member selected through a namespace re-export: the member is swept, the
// rest of its module, code included, is not.
export function f(
  x: keyof { z: typeof import("@fixture/relay").namespaced.value },
): "z" {
  return x;
}
