// A fresh result, `Fresh<T>`: refused while no source statement reaches its
// certification.
export function zeros(count: number): Fresh<number[]> {
  const out: number[] = [];
  for (let i = 0; i < count; i++) out.push(0);
  return out;
}
