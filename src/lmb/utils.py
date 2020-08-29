from typing import Callable
from z3 import z3

remove_ctx_index = r"\_[0-9]"

def group(func: Callable, iterable: list) -> list :
    groups = {}
    for e in iterable :
        tmp = func(e)
        if tmp not in groups :
            groups[tmp] = [e]
        else :
            groups[tmp] += [e]
    return [v for v in groups.values()]