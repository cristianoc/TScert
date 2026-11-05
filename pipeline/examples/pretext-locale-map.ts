// pretext: getWebKitLineRules and getWebKitGenericFamilies; cold own-entry lookup.
const rows = new Map<string, readonly number[]>([['', [1]], ['toString', [2]]])
export function lookup(name: string): number {
  let row = rows.get(name)
  while (row === undefined) {
    if (name === '') throw new RangeError('missing root')
    const cut = name.lastIndexOf('_')
    name = cut < 0 ? '' : name.slice(0, cut)
    row = rows.get(name)
  }
  const result = row[0]
  if (result === undefined) throw new RangeError('empty row')
  return result
}
