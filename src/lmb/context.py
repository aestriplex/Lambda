from sys import getsizeof

class Context :
    
    def __init__(self) :
        self._occurrencies = {}
        self._assertions = []

    def __src__(self) :
        return f"<Context ({getsizeof(self)})>"

    def __repr__(self) :
        return f"<Context ({getsizeof(self)}) at {hex(id(self))}>"

    def add(self,occurrence) :
        pass