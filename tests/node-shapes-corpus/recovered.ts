// Read by tests/compiler-api-shapes.mts, never run: a decorator no
// declaration follows, which the parser recovers as a missing declaration.
declare const dec: (target: unknown) => void;
@dec
