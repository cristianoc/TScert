// Writing a writable optional field adds the key where the object was
// allocated without it; the caller may hold the object, and see its keys
// change, so the write is refused.
type WithOptional = { opt?: number };
export function set(x: WithOptional): void {
  x.opt = 3;
}
