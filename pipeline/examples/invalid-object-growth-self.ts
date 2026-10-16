// The value written is the object itself: the field would hold the object
// the write adds the key to, so the write is refused.
export function grow(): {} {
  const o = {};
  o.self = o;
  return o;
}
