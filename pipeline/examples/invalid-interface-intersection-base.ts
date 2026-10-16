type Left = { readonly left: number };
type Right = { readonly right: string };
type Both = Left & Right;
interface Combined extends Both {
  readonly own: boolean;
}

export function missingRight(): Combined {
  return { left: 3, own: true } as Combined;
}
