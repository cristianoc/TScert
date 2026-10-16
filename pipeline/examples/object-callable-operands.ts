"use strict";

// Callback inputs and outputs may contain nested readonly object contracts.
function nestedCallback(
  consume: (input: { readonly payload: { readonly value: number } }) => {
    readonly value: number;
  },
  input: { readonly payload: { readonly value: number } },
): number {
  return consume(input).value;
}

// A callback that writes requires the same fixed contract as its argument.
function mutableCallback(input: { value: number }): number {
  const replace = (target: { value: number }): number => {
    target.value = 2;
    return target.value;
  };
  return replace(input);
}

// Optional fields can be stated in a receiver contract as in an ordinary input.
function optionalReceiver(input: { value?: number }): number {
  const read = function (this: { value?: number }): number {
    return 1;
  };
  return read.call(input);
}
