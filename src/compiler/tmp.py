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

class BodyTypeException(Exception) :
    
    def __init__(self,_t) :
        self.msg = f"Depth must be a list, not {_t.__name__}"
    
    def __str__(self) :
        return self.msg

class ScriptTypeException(Exception) :
    
    def __init__(self,_t) :
        self.msg = f"Script parameter must be an esprima.nodes.Script, not {_t.__name__}"
    
    def __str__(self) :
        return self.msg

class VarTypeException(Exception) :
    
    def __init__(self,_t) :
        self.msg = f"You must pass a string for parameter {_t.__name__} insted of {type(_t).__name__}"
    
    def __str__(self) :
        return self.msg
    
class VarKind(Enum) :
    var = 0
    const = 1
    
class VarType :
    literal = "Literal"
    obj = "ObjectExpression"

class Function :

    _name = None
    _block = None
    _params = []

    def __init__(self,src) :
        self._parse_fun(src)

    def __str__(self) :
        return f"<FUN: {self._name}>"

    def _parse_fun(self,src) :
        self._name = src.id.name
        self._params = [Variable(p.name,"var") for p in src.params]
        self._block = parse(src.body.body)
    
class Block :

    depth = None
    body = []

    def __init__(self,src,depth) :
        if type(src) != list :
            raise BodyTypeException(type(src))
        pass

    def __str__(self) :
        return f"<Block depth: {self.depth}>"

class Variable :

    def __init__(self,name,kind,value = None) :
        if type(name) != str :
            raise VarTypeException(name)

        self._name = name
        self._kind = kind
        self._value = value
    
    def __str__(self) :
        return f"<VAR: {self._name}>"

def _parse_variable(src, kind) :   
    kind = _get_kind(kind)
    name = src.id.name
    value = _get_var_value(src)
    return Variable(name,kind,value)    

def _get_var_value(src) :
    if src.init.type == VarType.literal :
        return src.init.value
    if src.init.type == VarType.obj :
        return _parse_object(src.init.properties)

def _parse_object(prop) :
    obj = {}
    for p in prop :
        obj.update({p.key.value : p.value.value})
    return obj

def _get_kind(k) :

        if k == "var" :
            return VarKind.var
        if k == "const" :
            return VarKind.const
        else :
            return None

def _get_variables(declarations, kind) :
    
    v = []
    for d in declarations :
        v.append(_parse_variable(d,kind))
    if v != [] :
        return v
    
def is_variable(element) :
    return element == var

def is_function(element) :
    return element == fun_declaration

def parse(src) :

    body = []
    for e in src :
        if is_function(e.type) :
            body.append(Function(e))
        if is_variable(e.type) :
            body += _get_variables(e.declarations,e.kind)
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
print(*l)