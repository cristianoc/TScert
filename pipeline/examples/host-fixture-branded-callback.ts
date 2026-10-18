// The host calls a client callback with its branded string, which the
// callback takes as a string (reading rule 5).
import { eachPath } from "@fixture/host";

export function lengths(): number {
  let total = 0;
  eachPath((path: string) => {
    total = total + path.length;
  });
  return total;
}
