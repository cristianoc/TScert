// Read by tests/compiler-api-shapes.mts, never run: JSDoc types and links,
// and statements only a sloppy-mode script has.
/**
 * @param {?number} a nullable, see {@link pair}
 * @param {!Object} b non-null, see {@linkcode pair}
 * @param {*} c anything, see {@linkplain pair}
 * @param {number=} d optional
 * @param {...number} e variadic
 * @param {function(number): string} f a function
 * @param {?} g unknown
 * @param {module:other.Thing} h a name path
 * @returns {Array.<number>} an array
 */
function documented(a, b, c, d, e, f, g, h) { return [a]; }
with (Math) { documented(PI); }
class Gaps { ; method() {} ; }
module.exports = { documented, Gaps };
