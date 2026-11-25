// Node witness: With extras = [], appendRows(extras) returns [[42]] and leaves extras equal to [[]].
/**
 * @ensures forall i in result: result[i] === null || extras[i] === null || result[i].length <= extras[i].length
 * @requires extras.length === 0
 */
export function appendRows(extras: (number[] | null)[]): (number[] | null)[] {
  const advances: (number[] | null)[] = [];
  const adv = [42];
  const ex: number[] = [];
  const i = advances.length;
  if ((i & 0x7fffffff) !== i || i > advances.length) throw new RangeError("index");
  advances[i] = adv;
  if ((i & 0x7fffffff) !== i || i > extras.length) throw new RangeError("index");
  extras[i] = ex;
  return advances;
}
