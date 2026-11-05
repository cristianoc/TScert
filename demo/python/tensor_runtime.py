"""Concrete failures and regression evidence for the assumed rank contracts."""
import hashlib
import importlib
import json
from pathlib import Path
import sys
import tempfile
import torch

root = Path(__file__).parent / "examples" / "tensors"
sys.path.insert(0, str(root))
bad = importlib.import_module('bad_errors').squared_error
fixed = importlib.import_module('fixed_errors').squared_error
squeeze_all = importlib.import_module('batch_squeeze').predict_vector
squeeze_last = importlib.import_module('fixed_squeeze').predict_vector
unchecked = importlib.import_module('unchecked_squeeze').predict_vector
loss = importlib.import_module('scalar_loss').loss
fixed_loss = importlib.import_module('fixed_loss').loss
evidence = Path(tempfile.mkdtemp(prefix='tscert-tensor-runtime-'))
report = {'torch': torch.__version__, 'python': sys.version, 'device': 'cpu', 'dtype': 'float32', 'samples': [], 'contracts': []}

def save():
    (evidence / 'runtime-report.json').write_text(json.dumps(report, indent=2))

for batch in [0, 1, 2, 8]:
    predictions = torch.arange(batch, dtype=torch.float32).reshape(batch, 1)
    targets = torch.arange(batch, dtype=torch.float32)
    assert bad(predictions, targets).shape == (batch, batch)
    assert fixed(predictions, targets).shape == (batch,)
    assert torch.equal(fixed(predictions, targets), torch.zeros(batch))
    assert squeeze_all(predictions).ndim == (0 if batch == 1 else 1)
    assert squeeze_last(predictions).shape == (batch,)
    assert unchecked(torch.zeros(batch, 3)).ndim == 2
    assert loss(predictions, targets).ndim == 0
    assert fixed_loss(predictions, targets).ndim == 0
    item = {'batch': batch, 'bad_errors_shape': list(bad(predictions, targets).shape),
            'fixed_errors_shape': list(fixed(predictions, targets).shape),
            'squeeze_all_rank': squeeze_all(predictions).ndim,
            'squeeze_last_rank': squeeze_last(predictions).ndim}
    if batch:
        item.update(wrong_loss=loss(predictions, targets).item(), fixed_loss=fixed_loss(predictions, targets).item())
    report['samples'].append(item)
    save()

# Different vector lengths exercise the actual native specification rather
# than the one same-batch counterexample. Every normal result meets its rank
# contract; an incompatible vector subtraction may raise, which the formal
# safety property permits. All operations here are out of place.
for rows in [0, 1, 2, 5]:
    for cols in [0, 1, 2, 5]:
        column = torch.arange(rows, dtype=torch.float32).reshape(rows, 1)
        vector = torch.arange(cols, dtype=torch.float32)
        before = (column.clone(), vector.clone(), column.shape, vector.shape)
        matrix = column - vector
        assert matrix.ndim == 2
        assert matrix.square().ndim == 2
        assert matrix.mean().ndim == 0
        assert vector.square().ndim == 1
        assert vector.mean().ndim == 0
        assert column.squeeze(-1).ndim == 1
        assert column.squeeze().ndim in (0, 1)
        normal = True
        try:
            difference = column.squeeze(-1) - vector
            assert difference.ndim == 1
        except RuntimeError:
            normal = False
        assert torch.equal(column, before[0]) and torch.equal(vector, before[1])
        assert column.shape == before[2] and vector.shape == before[3]
        report['contracts'].append({'rows': rows, 'cols': cols, 'vector_subtraction_returns': normal})
        save()

# The broadcast counterexample has perfectly matching predictions and labels.
p = torch.tensor([[1.0], [2.0]])
t = torch.tensor([1.0, 2.0])
assert loss(p, t).item() == 0.5 and fixed_loss(p, t).item() == 0.0
print(f'PyTorch {torch.__version__}: 4 batch sizes and 16 operator-contract combinations pass')
print('broadcasting: correct predictions yield wrong scalar loss 0.5; squeeze(-1) yields 0.0')
print('batch=1: squeeze() returns scalar; squeeze(-1) retains vector')
print('evidence:', evidence / 'runtime-report.json')
