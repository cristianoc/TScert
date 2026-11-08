export function readSubtags(locale: string): string {
  const subtags = locale.split(/[-_]/);
  let name = "";
  for (let k = 1; k < subtags.length; k++) {
    const subtag = subtags[k];
    if (subtag === undefined) throw new RangeError("missing value");
    name += "_" + subtag.toUpperCase();
  }
  return name;
}
