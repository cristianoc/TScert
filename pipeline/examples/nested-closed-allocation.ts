// Nested object literals inside unannotated local and module-level `const`
// bindings preserve their exact own-key bounds when their enclosing fields are
// not reassigned to open records or passed to mutable open-field contracts.
interface Resource {
  instantiate(input: number, extra: string): number;
}

type ResourceClass = new () => Resource;

interface Service {
  readonly inputs: { readonly [name: string]: number };
  readonly resources: { readonly [name: string]: ResourceClass };
  readonly run: (n: number) => number;
}

class Names implements Resource {
  instantiate(input: number): number {
    return input + 1;
  }
}

function acceptService(s: Service): number {
  const ctor = s.resources["names"];
  const init = s.inputs["count"];
  if (ctor !== undefined && init !== undefined) {
    return s.run(new ctor().instantiate(init, "ctx"));
  }
  return 0;
}

function acceptGeneric<T extends { readonly [k: string]: number }>(box: {
  readonly inner: T;
  readonly resources: { readonly [name: string]: ResourceClass };
}): number {
  const v = box.inner["a"];
  return v !== undefined ? v : 0;
}

const moduleService = {
  inputs: { count: 10 },
  resources: { names: Names },
  run: (n: number): number => n * 2,
};

export function useModuleConst(): number {
  return acceptService(moduleService);
}

export function useLocalConst(): number {
  const localService = {
    inputs: { count: 20 },
    resources: { names: Names },
    run: (n: number): number => n + 3,
  };
  return acceptService(localService);
}

export function useGenericAndInnerFieldMutation(): number {
  const box = {
    inner: { a: 1, b: 2 },
    resources: { names: Names },
  };
  // Mutating an existing property of `box.inner` keeps its exact own keys.
  box.inner.a = 42;
  return acceptGeneric(box);
}
