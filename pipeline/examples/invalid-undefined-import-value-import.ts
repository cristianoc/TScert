// An import may bind the name `undefined`; a read of it is that binding,
// here the imported number, not the value `undefined`. A name `undefined`
// TypeScript binds to anything but the global is refused where it is read.
import { limit as undefined } from "@fixture/lib";

export function read(): number | undefined {
  return undefined;
}
