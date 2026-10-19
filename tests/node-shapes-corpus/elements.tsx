// Read by tests/compiler-api-shapes.mts, never run: JSX forms.
declare const React: unknown;
const value = 1;
export const element = <div id="a" {...{ b: 1 }} data-x={value}>text {value}<br /><><span ns:attr="x" /></></div>;
