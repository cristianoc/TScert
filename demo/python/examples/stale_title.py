from typing import TypedDict


class Payload(TypedDict):
    title: str | int


def display_title(payload: Payload) -> str:
    alias = payload
    if isinstance(payload["title"], str):
        alias["title"] = 0
        return payload["title"]
    return "untitled"
