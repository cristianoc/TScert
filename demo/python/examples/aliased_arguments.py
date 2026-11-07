from typing import TypedDict


class Payload(TypedDict):
    title: str | int


def display_title(payload: Payload, pending: Payload) -> str:
    if isinstance(payload["title"], str):
        pending["title"] = 0
        return payload["title"]
    return "untitled"
