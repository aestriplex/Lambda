from __future__ import annotations
import re
from typing import Any
from enum import Enum
from .utils import remove_ctx_index
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
        else :
            self._occurrencies, self._types = self._get_from_parent(parent)
        self._parent = parent

    def __src__(self) -> str :
        var = "var" if len(self._occurrencies) == 1 else "vars"
        return f"<Context ({len(self._occurrencies)} {var})>"

    def __repr__(self) -> str :
        var = "var" if len(self._occurrencies) == 1 else "vars"
        return f"<Context ({len(self._occurrencies)} {var}) at {hex(id(self))}>"

    def _get_from_parent(self, parent_ctx: Context) -> tuple :
        parent_occ, parent_types = parent_ctx.get_content()
        return parent_occ.copy(), parent_types.copy()
    
    def get_content(self) -> tuple :
        return self._occurrencies, self._types
    
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

    def get_type(self, occurrence: str) :
        label = re.sub(remove_ctx_index,"",occurrence)
        
        if label not in self._types :
            if self._parent is not None :
                return self._parent.get_type(occurrence)
            raise VariableMissingException(label)

        return self._types[label]

    def set_parent(self, parent: Context) -> None :
        self._parent = parent

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