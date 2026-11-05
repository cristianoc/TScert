from rank_contracts import Column, Vector


def squared_error(predictions: Column, targets: Vector) -> Vector:
    return (predictions.squeeze(-1) - targets).square()
