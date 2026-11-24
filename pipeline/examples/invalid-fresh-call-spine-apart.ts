// Without `Fresh`, a helper returning an array may alias a field-rooted array:
// writing at its end grows `data.widths` past `data.flags.length`.
function shared(data: {
  readonly flags: Uint8Array;
  readonly widths: number[];
}): Modifies<{}, number[]> {
  return data.widths;
}

/**
 * @requires data.flags.length === data.widths.length
 */
export function growThroughAlias(data: {
  readonly flags: Uint8Array;
  readonly widths: number[];
}): number {
  const spaces = shared(data);
  const end = spaces.length;
  if ((end & 0x7fffffff) !== end || end > spaces.length)
    throw new RangeError("index");
  spaces[end] = 99;
  const last = data.widths.length - 1;
  return data.flags[last]! + 1;
}
