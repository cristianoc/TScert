from typing import TypedDict


class Payload(TypedDict):
    title: str | int


def display_title(payload: Payload, replacement: str | int) -> str:
    alias = payload
    alias["title"] = replacement
    if isinstance(payload["title"], str):
        return payload["title"]
    return "untitled"


def title_with_suffix(payload: Payload, replacement: str | int) -> str:
    alias = payload
    alias["title"] = replacement
    if isinstance(payload["title"], str):
        return payload["title"] + "!"
    return "untitled"
