import esprima
from enum import Enum

var = "VariableDeclaration"
expr = "ExpressionStatement"
fun_declaration = "FunctionDeclaration"
fun_expr = ["FunctionExpression","ArrowFunctionExpression"]
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

class Body :
    
    def __init__(self,_type) :
        self._type = _type
    
    def __str__(self) :
        return f"{type(self._type).__name__}"
    
class VarKind(Enum) :
    var = 0
    const = 1
    
class VarType :
    literal = "Literal"
    obj = "ObjectExpression"

class Function :

    def __init__(self) :
        pass

    def __str__(self) :
        pass

class Variable :

    _name = None
    _kind = None
    _value = None
    
    def __init__(self, src, kind) :
        
        self._kind = self._get_kind(kind)
        self._parse_var(src)
        
    def __str__(self) :
        return f"<{self._name}, {self._value}, {self._kind}>"
    
    def _parse_var(self,src) :
        self._name = src.id.name
        self._value = self._get_value(src)
    
    def _get_value(self,src) :
        if src.init.type == VarType.literal :
            return src.init.value
        if src.init.type == VarType.obj :
            return self._parse_object(src.init.properties)
    
    def _parse_object(self,prop) :
        obj = {}
        for p in prop :
            obj.update({p.key.value : p.value.value})
        return obj
    
    def _get_kind(self,k) :

        if k == "var" :
            return VarKind.var
        if k == "const" :
            return VarKind.const

def _parse_variable(declarations, kind) :
    
    v = []
    for d in declarations :
        v.append(Variable(d,kind))
    if v != [] :
        return v
    
def is_variable(element) :
    return element == var

def is_function(element) :
    return element == fun_declaration

def parse(src) :

    body = []
    for e in src :
        if is_variable(e.type) :
            body += _parse_variable(e.declarations,e.kind)

    return body

with open("/Users/teo/Desktop/notebooks/a.js","r") as f :
    aaa = f.read()
try :
    source = esprima.parseScript(aaa)
except Exception as ex:
    print(f"ERROR: {ex}")
    exit()
print(source.body)
l = parse(source.body)
#print(*l)