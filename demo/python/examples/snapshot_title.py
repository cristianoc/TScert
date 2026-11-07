from typing import TypedDict


class Payload(TypedDict):
    title: str | int


def display_title(payload: Payload) -> str:
    alias = payload
    title = payload["title"]
    if isinstance(title, str):
        alias["title"] = 0
        return title
    return "untitled"
