"""Rank-only contracts: no relationship between different batch lengths."""
from typing import Annotated
from torch import Tensor

Scalar = Annotated[Tensor, "ndim=0"]
Vector = Annotated[Tensor, "ndim=1"]
Matrix = Annotated[Tensor, "ndim=2"]
Column = Annotated[Tensor, "ndim=2; last_dimension=1"]
