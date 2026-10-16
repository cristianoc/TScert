// A recursive pair's meet reads its operands' fields at their own types: the
// value of a leaf of strings is no number.
interface TreeNode<T> {
  left: TreeNode<T> & TreeLeaf<T>;
  right: TreeNode<T>;
}
interface TreeLeaf<T> {
  value: T;
  parent: TreeNode<T> & TreeLeaf<T>;
}
export function bad(x: TreeNode<string> & TreeLeaf<string>): number {
  return x.left.value;
}
