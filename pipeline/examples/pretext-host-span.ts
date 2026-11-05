// pretext: readEmojiWidth and readWidthIn.
export function measure(font: string): number {
  const parent = document.body ?? document.documentElement
  if (parent === null) return NaN
  const span = document.createElement('span')
  const style = span.style
  if (style === undefined) throw new RangeError('missing inline style')
  style.cssText = 'display:inline-block'
  style.setProperty('font', font, 'important')
  span.textContent = 'hello'
  parent.appendChild(span)
  const width = span.getBoundingClientRect().width
  parent.removeChild(span)
  return width
}
