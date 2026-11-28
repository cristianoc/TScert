// Importing a symbol declared as both an `interface` and a companion `const`
// resolves the interface in type position and the const in value position.
import { ServiceHandle, openHandle } from "@fixture/merged-interface-value";

export function checkHandle(handle: ServiceHandle): boolean {
  const fresh = openHandle();
  const constructed: ServiceHandle = new ServiceHandle(fresh.id);
  return handle.ping() && constructed.ping();
}
