from rank_contracts import Column, Vector


def predict_vector(predictions: Column) -> Vector:
    return predictions.squeeze()
