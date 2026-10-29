// A URL-valued input can invoke own getters and lazy serialization hooks.
import { fileURLToPath } from "node:url";
export function pathOf(url: URL): string {
  return fileURLToPath(url);
}
