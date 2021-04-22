import sys
from typing import Any, Hashable
from .exceptions import SegmentationFaultException

class MemoryMap :
    """
    Memory map implementation
    """

    _map = {}
    _reversed_map = {}
    _available = []
    _objs = []

    def __init__(self) -> None :
        self._map[hex(0)] = None
        self._reversed_map[None] = hex(0)

    def __str__(self) -> str :
        return f"<MemoryMap ({sys.getsizeof(self)})>"

    def __repr__(self) -> str :
        return f"<MemoryMap at ({hex(id(self))})>"
    
    def _next_addr(self) -> str :
        if self._available :
            addr = self._available.pop(0)
        else :
            addr = int([k for k in self._map][-1],16) + 1
        return hex(addr)

    def add(self, value: Hashable) -> str :
        if value in self._reversed_map :
            address = self._reversed_map[value]
        else :
            address = self._next_addr()
            self._map[address] = value
            self._reversed_map[value] = address
        return address
    
    def get(self, addr: str) -> Any :
        if addr not in self._map :
            raise SegmentationFaultException(addr)
        return self._map[addr]

    def get_by_value(self, val: Hashable) -> str :
        if val not in self._reversed_map :
            raise Exception()
        return self._reversed_map[val]

    def remove_by_addr(self, addr: str) -> None :
        val = self._map[addr]
        if val :
            self._available.append(addr)
            del self._map[addr]
            del self._reversed_map[val]

    def remove(self, value: Hashable) -> None :
        address = self._reversed_map[value]
        if address :
            self._available.append(address)
            del self._reversed_map[value]
            del self._map[address]

    def dump(self) -> dict :
        return self._map
