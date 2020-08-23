from __future__ import annotations
from enum import Enum
from .exceptions import VariableMissingException

class Label(Enum) :
    curr   = 0x00
    prev = 0x01

class Context :

    def __init__(self, parent: Context = None) -> None :
        self._occurrencies = {}
        self._assertions = []
        self.parent = parent

    def __src__(self) -> str :
        var = "var" if len(self._occurrencies) == 1 else "vars"
        return f"<Context ({len(self._occurrencies)} {var})>"

    def __repr__(self) -> str :
        var = "var" if len(self._occurrencies) == 1 else "vars"
        return f"<Context ({len(self._occurrencies)} {var}) at {hex(id(self))}>"

    def add(self, occurrence: str) -> None :
        if occurrence not in self._occurrencies :
            self._occurrencies.update({occurrence : 0})
        else :
            self._occurrencies[occurrence] += 1

    def get_label(self, var_name: str, var_type: Label, is_embedded: bool = False) -> str :
        if var_name not in self._occurrencies :
            raise VariableMissingException(var_name)

        n_occurrence = self._occurrencies[var_name]
        if var_type == Label.curr :
            n_occurrence = self._occurrencies[var_name] + 1
        if is_embedded :
            return f"{var_name}"
        return f"{var_name}_{n_occurrence}"