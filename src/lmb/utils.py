from typing import Callable
from z3 import z3, Int, Real, String

remove_ctx_index = r"\_[0-9]"
remove_var_name = r"[a-zA-z]*\_"

def get_z3_type(name: str, t: object) -> z3 :
    if t == int :
        return Int(name)
    elif t == float :
        return Real(name)
    elif t == str :
        return String(name)

def group(func: Callable, iterable: list) -> list :
    groups = {}
    for e in iterable :
        tmp = func(e)
        if tmp not in groups :
            groups[tmp] = [e]
        else :
            groups[tmp] += [e]
    return [v for v in groups.values()]