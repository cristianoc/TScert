"""Compare actual Tensor annotations, with torch installed in this interpreter."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile

root = Path(__file__).parent / "examples" / "tensors"
evidence = Path(tempfile.mkdtemp(prefix="tscert-tensor-comparison-"))
files = [str(root / f'{name}.py') for name in [
    'bad_errors', 'fixed_errors', 'batch_squeeze', 'fixed_squeeze',
    'unchecked_squeeze', 'scalar_loss',
]]
config = evidence / 'pyrightconfig.json'
config.write_text(json.dumps({'typeCheckingMode': 'strict', 'pythonVersion': '3.13', 'extraPaths': [str(root)]}))
control = evidence / 'ordinary_error.py'
control.write_text('from torch import Tensor\n\ndef ordinary_error(x: Tensor) -> Tensor:\n    return 0\n')
tools = [
    ('mypy', ['--strict', '--no-incremental', '--cache-dir', str(evidence / 'mypy-cache')]),
    ('pyright', ['--project', str(config), '--pythonpath', sys.executable]),
    ('basedpyright', ['--project', str(config), '--pythonpath', sys.executable]),
    ('ty', ['check', '--python', sys.executable]),
    ('pyrefly', ['check', '--preset', 'strict', '--python-interpreter-path', sys.executable]),
]
report = {'python': sys.executable, 'sources': {f: hashlib.sha256(Path(f).read_bytes()).hexdigest() for f in files}, 'runs': []}
def run(name, args):
    p = subprocess.run([name, *args], cwd=root, capture_output=True, text=True, timeout=180)
    r = {'command': [name, *args], 'status': p.returncode, 'stdout': p.stdout, 'stderr': p.stderr}
    report['runs'].append(r)
    (evidence / 'checker-report.json').write_text(json.dumps(report, indent=2))
    return p
print('evidence:', evidence, flush=True)
for name, options in tools:
    version = run(name, ['--version'])
    assert version.returncode == 0, version.stderr
    sample = run(name, [*options, *files])
    assert sample.returncode == 0, sample.stdout + sample.stderr
    error = run(name, [*options, str(control)])
    assert error.returncode == 1 and 'ordinary_error.py' in error.stdout + error.stderr, error.stdout + error.stderr
    print(version.stdout.strip(), ': accepts all six tensor cases; rejects ordinary Tensor return error', flush=True)
