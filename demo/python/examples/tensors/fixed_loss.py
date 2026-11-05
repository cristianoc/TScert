from rank_contracts import Column, Vector, Scalar


def loss(predictions: Column, targets: Vector) -> Scalar:
    return (predictions.squeeze(-1) - targets).square().mean()
