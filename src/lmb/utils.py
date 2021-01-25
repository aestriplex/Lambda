from typing import Callable
from z3 import z3, Int, Real, String

remove_ctx_index = r"\_[0-9]"
remove_var_name = r".*\_"

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

def _merge_int_dict(first: dict, second: dict, comp: Callable) -> dict :
    out = {}
    for k in first :
        if k not in second or comp(first[k],second[k]) :
            out[k] = first[k]
        else :
            out[k] = second[k]
    for k in second :
        if k not in first :
            if k not in out or comp(second[k],first[k]) :
                out[k] = second[k]
            else :
                out[k] = first[k]
    return out

def merge_int_dict_max(first: dict, second: dict) -> dict :
    """
    Merge two integer-valued dictionaries.

    If a key is contained in both, it takes the maximum value.
    """
    return _merge_int_dict(first,second,lambda x,y: x>y)

def merge_int_dict_min(first: dict, second: dict) -> dict :
    """
    Merge two integer-valued dictionaries.

    If a key is contained in both, it takes the minimum value.
    """
    return _merge_int_dict(first,second,lambda x,y: x<y)

def merge_any_dict(first: dict, second: dict) -> dict :
    """
    """
    out = {}
    for k in first :
        out[k] = first[k] if k not in second else second[k]
           
    for k in second :
        if k not in first :
            out[k] = second[k] if k not in out else first[k]
               
    return out