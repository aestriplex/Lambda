from __future__ import annotations
import re
import sys
from typing import Any
from enum import Enum
from .utils import remove_ctx_index, merge_int_dict_max, merge_any_dict
from .exceptions import VariableMissingException, ImplicitlyTypedException

class Label(Enum) :
    """
    """
    curr   = 0x00
    prev = 0x01

class Context() :
    """
    """
    def __init__(self, parent: Context = None) -> None :
        if parent is None :
            self._occurrencies = {}
            self._types = {}
            self._functions = {}
        else :
            self._occurrencies, self._types = self._get_from_parent(parent)
        self._parent = parent

    def __src__(self) -> str :
        var = "var" if len(self._occurrencies) == 1 else "vars"
        return f"<Context ({len(self._occurrencies)} {var})>"

    def __repr__(self) -> str :
        var = "var" if len(self._occurrencies) == 1 else "vars"
        return f"<Context ({len(self._occurrencies)} {var}) at {hex(id(self))}>"

    def update(self, name: str, n_occurrencies: int) -> None :
        if name in self._occurrencies:
            self._occurrencies[name] = n_occurrencies
        else :
            raise VariableMissingException(name)

    def get_context_size(self) -> dict :
        size = {}
        obj = self.__dict__
        for key, value in obj.items() :
            size.update({key : sys.getsizeof(value)})
        return size

    def _get_from_parent(self, parent_ctx: Context) -> tuple :
        parent_occ, parent_types = parent_ctx.get_content()
        return parent_occ.copy(), parent_types.copy()
    
    def get_content(self) -> tuple :
        return self._occurrencies, self._types

    def get_occurrencies(self) -> dict :
        return self._occurrencies

    def get_types(self) -> dict :
        return self._types
    
    def get_last_update_vars(self) -> list :
        return [f"{k}_{self._occurrencies[k]}" for k in self._occurrencies.keys()]

    def add(self, occurrence: str, _type: Any = None) -> None :
        """
        """
        if occurrence not in self._occurrencies :
            self._occurrencies.update({occurrence : 0})

            if _type is None :
                ImplicitlyTypedException(occurrence)

            if occurrence not in self._types :
                self._types.update({occurrence : _type})
        else :
            self._occurrencies[occurrence] += 1
    
    def add_function(self, fun: Any) -> None :
        name = fun.get_name()
        self._functions[name] = fun
    
    def get_functions(self) -> dict :
        return self._functions

    def get_type(self, occurrence: str) :
        label = re.sub(remove_ctx_index,"",occurrence)
        
        if label not in self._types :
            if self._parent is not None :
                return self._parent.get_type(occurrence)
            raise VariableMissingException(label)

        return self._types[label]

    def set_parent(self, parent: Context) -> None :
        self._parent = parent

    def set_occurrencies(self, occ: dict) -> None :
        self._occurrencies = occ
    
    def set_types(self, types: dict) -> None :
        self._types = types

    def set_functions(self, functions: dict) -> None :
        self._functions = functions

    def get_label(self, var_name: str, var_type: Label) -> str :
        """
        """
        if var_name not in self._occurrencies :
            if self._parent is not None :
                return self._parent.get_label(var_name, var_type)
            raise VariableMissingException(var_name)

        n_occurrence = self._occurrencies[var_name]
        if var_type == Label.curr :
            n_occurrence += 1
        
        return f"{var_name}_{n_occurrence}"
    
    @staticmethod
    def merge_context(ctx1: Context, ctx2: Context) -> Context :
        new_ctx = Context()
        occurrencies = merge_int_dict_max(ctx1.get_occurrencies(),ctx2.get_occurrencies())
        #functions = merge_any_dict(ctx1.get_functions(),ctx2.get_functions())
        types = merge_any_dict(ctx1.get_types(),ctx2.get_types())
        
        new_ctx.set_occurrencies(occurrencies)
        #new_ctx.set_functions(functions)
        new_ctx.set_types(types)
        return new_ctx