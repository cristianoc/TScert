// A guard's answer held in a constant across forty loops, each loop head a
// cut, then an element read typed `number` that an empty array leaves
// `undefined`: `walk([], undefined)` returns `undefined` under Node. The
// guarded add needs the implication the loop heads carry, which the search's
// later rounds seed; every round fails at the read, and the first round's
// failure, at the add's edge, is the one reported. The function lowers to
// about 1,800 nodes, and each failing round searches all of them.
export function walk(xs: readonly number[], v: number | undefined): number {
  const has = v !== undefined;
  let total = 0;
  for (let i0 = 0; i0 < xs.length; i0++) total += xs[i0] ?? 0;
  for (let i1 = 0; i1 < xs.length; i1++) total += xs[i1] ?? 1;
  for (let i2 = 0; i2 < xs.length; i2++) total += xs[i2] ?? 2;
  for (let i3 = 0; i3 < xs.length; i3++) total += xs[i3] ?? 3;
  for (let i4 = 0; i4 < xs.length; i4++) total += xs[i4] ?? 4;
  for (let i5 = 0; i5 < xs.length; i5++) total += xs[i5] ?? 5;
  for (let i6 = 0; i6 < xs.length; i6++) total += xs[i6] ?? 6;
  for (let i7 = 0; i7 < xs.length; i7++) total += xs[i7] ?? 7;
  for (let i8 = 0; i8 < xs.length; i8++) total += xs[i8] ?? 8;
  for (let i9 = 0; i9 < xs.length; i9++) total += xs[i9] ?? 9;
  for (let i10 = 0; i10 < xs.length; i10++) total += xs[i10] ?? 10;
  for (let i11 = 0; i11 < xs.length; i11++) total += xs[i11] ?? 11;
  for (let i12 = 0; i12 < xs.length; i12++) total += xs[i12] ?? 12;
  for (let i13 = 0; i13 < xs.length; i13++) total += xs[i13] ?? 13;
  for (let i14 = 0; i14 < xs.length; i14++) total += xs[i14] ?? 14;
  for (let i15 = 0; i15 < xs.length; i15++) total += xs[i15] ?? 15;
  for (let i16 = 0; i16 < xs.length; i16++) total += xs[i16] ?? 16;
  for (let i17 = 0; i17 < xs.length; i17++) total += xs[i17] ?? 17;
  for (let i18 = 0; i18 < xs.length; i18++) total += xs[i18] ?? 18;
  for (let i19 = 0; i19 < xs.length; i19++) total += xs[i19] ?? 19;
  for (let i20 = 0; i20 < xs.length; i20++) total += xs[i20] ?? 20;
  for (let i21 = 0; i21 < xs.length; i21++) total += xs[i21] ?? 21;
  for (let i22 = 0; i22 < xs.length; i22++) total += xs[i22] ?? 22;
  for (let i23 = 0; i23 < xs.length; i23++) total += xs[i23] ?? 23;
  for (let i24 = 0; i24 < xs.length; i24++) total += xs[i24] ?? 24;
  for (let i25 = 0; i25 < xs.length; i25++) total += xs[i25] ?? 25;
  for (let i26 = 0; i26 < xs.length; i26++) total += xs[i26] ?? 26;
  for (let i27 = 0; i27 < xs.length; i27++) total += xs[i27] ?? 27;
  for (let i28 = 0; i28 < xs.length; i28++) total += xs[i28] ?? 28;
  for (let i29 = 0; i29 < xs.length; i29++) total += xs[i29] ?? 29;
  for (let i30 = 0; i30 < xs.length; i30++) total += xs[i30] ?? 30;
  for (let i31 = 0; i31 < xs.length; i31++) total += xs[i31] ?? 31;
  for (let i32 = 0; i32 < xs.length; i32++) total += xs[i32] ?? 32;
  for (let i33 = 0; i33 < xs.length; i33++) total += xs[i33] ?? 33;
  for (let i34 = 0; i34 < xs.length; i34++) total += xs[i34] ?? 34;
  for (let i35 = 0; i35 < xs.length; i35++) total += xs[i35] ?? 35;
  for (let i36 = 0; i36 < xs.length; i36++) total += xs[i36] ?? 36;
  for (let i37 = 0; i37 < xs.length; i37++) total += xs[i37] ?? 37;
  for (let i38 = 0; i38 < xs.length; i38++) total += xs[i38] ?? 38;
  for (let i39 = 0; i39 < xs.length; i39++) total += xs[i39] ?? 39;
  if (has) total += v;
  const first: number = xs[0];
  return total > 0 ? total : first;
}
