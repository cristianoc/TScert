// `read` is correct at the constants' annotations, but initialization calls
// it before `late` holds a value: that read would throw.
function read(): boolean {
  return late;
}
const early: boolean = read();
const late: boolean = true;
