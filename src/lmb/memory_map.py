from typing import Any

class MemoryMap :
    """
    First implementation: no deallocation method
    """

    _map = {}

    def __init__(self) -> None :
        self._map[hex(0)] = None

    def __str__(self) -> str :
        return f""

    def __repr__(self) -> str :
        return f""
    
    def _next_addr(self) -> str :
        addr = int([k for k in self._map][-1],16) + 1
        return hex(addr)

    def add(self, value: Any) -> str :
        address = self._next_addr()
        self._map[address] = value
        return address