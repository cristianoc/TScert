// A span measured in the page as pretext's readEmojiWidth and readWidthIn
// measure one: its creation, its inline style's writes, its text, its
// insertion and removal and its rectangle run no code of the program's and
// write nothing the model holds, so a loop's bound on an array holds across
// each measurement.
function readWidthIn(parent: Element, span: Element): number {
  parent.appendChild(span)
  const drawn = span.getBoundingClientRect().width
  const width = parseFloat(getComputedStyle(span).width)
  parent.removeChild(span)
  return Math.abs(drawn - width) <= width * 1e-5 ? drawn : width
}

function measure(font: string): number {
  const body = document.body
  if (body === null) return NaN
  const span = document.createElement('span')
  const style = span.style
  if (style === undefined) throw new RangeError('missing inline style')
  style.cssText = 'display:inline-block!important'
  style.setProperty('font', font, 'important')
  span.textContent = '\u{1F600}'
  return readWidthIn(body, span)
}

export function total(fonts: string[]): number {
  let sum = 0
  for (let i = 0; i < fonts.length; i++) sum += measure(fonts[i]!) + fonts[i]!.length
  return sum
}
