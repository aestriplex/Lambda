from enum import Enum
from .exceptions import VariableMissingException

class Label(Enum) :
    curr   = 0x00
    prev = 0x01

class Context :

    def __init__(self) -> None :
        self._occurrencies = {}
        self._assertions = []

    def __src__(self) -> str :
        return f"<Context ({len(self._occurrencies)} vars)>"

    def __repr__(self) -> str :
        return f"<Context ({len(self._occurrencies)} vars) at {hex(id(self))}>"

    def add(self, occurrence: str) -> None :
        if occurrence not in self._occurrencies :
            self._occurrencies.update({occurrence : 0})
        else :
            self._occurrencies[occurrence] += 1

    def get_label(self, var_name: str, var_type: Label) -> str :
        if var_name not in self._occurrencies :
            raise VariableMissingException(var_name)

        n_occurrence = self._occurrencies[var_name]
        if var_type == Label.curr :
            n_occurrence = self._occurrencies[var_name] + 1
        return f"{var_name}_{n_occurrence}"