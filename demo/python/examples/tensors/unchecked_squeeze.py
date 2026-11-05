from rank_contracts import Matrix, Vector


def predict_vector(predictions: Matrix) -> Vector:
    return predictions.squeeze(-1)
