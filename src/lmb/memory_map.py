from typing import Any, Hashable
from .exceptions import SegmentationFaultException

class MemoryMap :
    """
    Memory map implementation
    """

    def __init__(self) -> None :
        self._map = {}
        self._reversed_map = {}
        self._available = []

        self._map[hex(0)] = None

    def __str__(self) -> str :
        return "<MemoryMap>"

    def __repr__(self) -> str :
        return f"<MemoryMap at ({hex(id(self))})>"
    
    def _next_addr(self) -> str :
        if self._available :
            addr = self._available.pop(0)
        else :
            addr = int([k for k in self._map][-1],16) + 1
        return hex(addr)

    def add(self, value: Hashable) -> str :
        current = self._reversed_map[value]
        if current :
            address = current
        else :
            address = self._next_addr()
            self._map[address] = value
            self._reversed_map[value] = address
        return address
    
    def get(self, addr: str) -> Any :
        if addr not in self._map :
            raise SegmentationFaultException(addr)
        return self._map[addr]

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