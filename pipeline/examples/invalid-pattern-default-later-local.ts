// A default of an object pattern reading a later local reads that binding
// before its initialization (JavaScript throws there when the key is
// absent): the binding is early, and unannotated it is refused. Its key
// `stated` reads no binding.
export function size(entry: { stated?: number; name: string }): number {
  const { stated: written = stated, ...rest } = entry;
  const stated = written + rest.name.length;
  return stated;
}
