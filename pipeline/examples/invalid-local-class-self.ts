// A class declared in a block whose method constructs the class by its own
// name: refused at the read.
export function cloned(): object {
  class Node {
    copy(): Node {
      return new Node();
    }
  }
  return new Node().copy();
}
