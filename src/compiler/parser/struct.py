import esprima
from .exceptions import ScriptTypeException
from .types.blocktypes import VarType

class Variable :

    _name = None
    _kind = None
    _value = None
    
    def __init__(self, src, kind) :
        
        if type(src) != esprima.nodes.Script :
            raise ScriptTypeException(type(src))
        
        self._kind = self._get_kind(kind)
        self._parse_var(src)
    
    def _parse_var(self,src) :
        self._name = src.id.name
        self._value = src.init.value
    
    def _get_kind(self,k) :

        if k == "var" :
            return VarType.var
        if k == "const" :
            return VarType.const