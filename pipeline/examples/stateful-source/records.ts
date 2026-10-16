// Independent locations, lexical initializer order, and a captured field guard.
function recordAlias(seed: boolean): boolean {
  const record: { left: boolean; right: boolean } = {
    left: seed,
    right: false,
  };
  const alias = record;
  alias.right = true;
  return record.left;
}

function recordOrder(): boolean {
  const cell: { value: boolean } = { value: false };
  const record: { before: boolean; write: boolean; after: boolean } = {
    before: cell.value,
    write: (cell.value = true),
    after: cell.value,
  };
  return record.before;
}

function recordGuard(seed: boolean | null): boolean {
  const record: { flag: boolean | null; other: boolean } = {
    flag: seed,
    other: true,
  };
  const read = (): boolean => (record.flag === null ? false : record.flag);
  return read();
}

function callableRecord(seed: boolean): boolean {
  const f = Object.assign<
    (x: boolean) => boolean,
    { left: boolean; right: boolean }
  >((x: boolean): boolean => x, { left: seed, right: false });
  f.right = true;
  return f.call(null, f.left);
}

// Contract order is not initializer order, including on callable objects.
function reorderedCallable(): boolean {
  const f = Object.assign<() => boolean, { right: boolean; left: boolean }>(
    (): boolean => true,
    { left: false, right: true },
  );
  return f.left;
}
// A number is an ordinary field contract: interned rather than refused, and
// invariant on its own location like any other.
function numericField(seed: number | null): number | null {
  const box: { count: number | null; flag: boolean } = {
    count: seed,
    flag: true,
  };
  if (box.flag) {
    box.count = null;
  }
  return box.count;
}

// One field, named by the program rather than by the model.
function singleNamedField(seed: boolean): boolean {
  const box: { other: boolean } = { other: seed };
  const alias = box;
  alias.other = true;
  return box.other;
}
