function missing(): never {
  throw new RangeError("missing value");
}

export function afterAtomic(atomic: boolean[], starts: number[] | null, text: string): number {
  let total = 0;
  for (let k = 0; k < atomic.length; k++) {
    if (!atomic[k]) continue;
    let after = ((starts ?? missing())[k] ?? missing()) + 1;
    while (after < text.length && text.charCodeAt(after) === 0) after++;
    total += after;
  }
  return total;
}

export function catchMissing(fail: boolean): number {
  try {
    return (fail ? missing() : 1) + 1;
  } catch {
    return 0;
  }
}
