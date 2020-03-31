# TODO: build package

import esprima

var = "VariableDeclaration"
fun = ["FunctionDeclaration", "FunctionExpression","ArrowFunctionExpression"]
declarator = ["VariableDeclarator","ObjectDeclarator"]

class DepthTypeException(Exception) :
    
    def __init__(self,_t) :
        self.msg = f"Depth must be an integer, not {_t.__name__}"
    
    def __str__(self) :
        return self.msg

class ScriptTypeException(Exception) :
    
    def __init__(self,_t) :
        self.msg = f"Script parameter must be an esprima.nodes.Script, not {_t.__name__}"
    
    def __str__(self) :
        return self.msg

class Scope :
    pass

class Body :
    
    def __init__(self) :
        self._contempt = []
    
    def __str__(self) :
        return f"{*self._contempt}"

    def push(self,obj) :
        pass

class Variable :

    _name = None
    _t = None
    _value = None
    
    def __init__(self, src, depth) :
        
        if type(depth) != int :
            raise DepthTypeException(type(depth))
            
        self.depth = depth
        self._parse_var(src)
    
    def _parse_var(self,src) :
        pass


body = Body()

def parse(src) :
    
    if type(src) != esprima.nodes.Script :
        raise ScriptTypeException(type(src))
        
    for e in src :
        if e.type == var :
            pass

with open("a.js","r") as f :
    aaa = f.read()
    source = esprima.parseScript(aaa)