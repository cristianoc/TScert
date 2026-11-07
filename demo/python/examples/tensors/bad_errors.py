from rank_contracts import Column, Vector


def squared_error(predictions: Column, targets: Vector) -> Vector:
    return (predictions - targets).square()
