// A generic class's method returns the instance's type argument, not another.
import { Keeper } from "@fixture/lib";
export function wrong(flag: boolean): null {
  return new Keeper<boolean>(flag).get();
}
