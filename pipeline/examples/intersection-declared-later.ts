// An intersection may name declarations whose equations are lowered after
// it, or are being lowered around it: a dictionary met with a record declared
// below, two index signatures, and a recursive pair whose fields meet the two
// declarations again.
type Named = Indexed & HasName;
type BothIndexes = Indexed & NumberIndexed;
interface Indexed {
  [key: string]: number;
}
interface NumberIndexed {
  [key: number]: number;
}
interface HasName {
  name: number;
}
interface TreeNode<T> {
  left: TreeNode<T> & TreeLeaf<T>;
  right: TreeNode<T>;
}
interface TreeLeaf<T> {
  value: T;
  parent: TreeNode<T> & TreeLeaf<T>;
}
function key(x: Named): number | undefined {
  return x["key"];
}
function name(x: Named): number {
  return x.name;
}
function position(x: BothIndexes): number | undefined {
  return x[0];
}
function leafValue(x: TreeNode<string> & TreeLeaf<string>): string {
  const y: TreeLeaf<string> = x.left;
  return y.value + x.parent.left.value;
}
export function use(x: Named, t: TreeNode<string> & TreeLeaf<string>): number {
  return name(x) + (key(x) ?? 0) + (position(x) ?? 0) + leafValue(t).length;
}
