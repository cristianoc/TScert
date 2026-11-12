// Store-boundary controls over a captured fragment with implementation imports,
// run alone; the suite of the single pass's controls runs the same controls
// (tests/single-pass-controls.mts).
// node dev/module-interface-controls.mts <fragment.json> <given.jsonl> <scratch>
import { interfaceControls } from "../tests/single-pass-control-inputs.mts";

const [fragment, given, scratch] = process.argv.slice(2);
if (!fragment || !given || !scratch) throw Error("fragment, given, scratch required");
interfaceControls(fragment, given, scratch, (line) => console.log(line));
