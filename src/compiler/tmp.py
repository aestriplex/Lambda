import esprima
from enum import Enum

var = "VariableDeclaration"
expr = "ExpressionStatement"
up_expr = "UpdateExpression"
bin_expr = "BinaryExpression"
ass_expr = "AssignmentExpression"
cond_expr = "IfStatement"
for_statement = "ForStatement"
while_statement = "WhileStatement"
do_while_statement = "DoWhileStatement"
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

class LoopKind(Enum) :
    for_loop = 0
    while_loop = 1
    do_while_loop = 2

class ExprKind(Enum) :
    binary = 0
    assignment = 1
    update = 2
    
class VarType :
    literal = "Literal"
    obj = "ObjectExpression"

class Expression :

    def __init__(self,kind,operator,first,second = None) :
        self.kind = kind
        self.operator = operator
        self.first = first
        self.second = second

    def __str__(self) :
        return f"<Expr: {self.operator}>"

class Conditional :

    def __init__(self,test,if_block,else_block) :
        self.test = test
        self.first = if_block
        self.second = else_block

    def __str__(self) :
        return f"<Conditional>"

class Loop :

    def __init__(self,kind,test,body) :
        self.kind = kind
        self.test = test
        self.body = body
    
    def __str__(self) :
        return f"<Loop: {self.kind}>"

class Function :

    def __init__(self,src) :
        self._name = src.id.name
        self._params = [Variable(p.name,"var") for p in src.params]
        self._block = parse(src.body.body)

    def __str__(self) :
        return f"<FUN: {self._name}>"

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
        if k == bin_expr :
            return ExprKind.binary
        if k == up_expr :
            return ExprKind.update
        if k == ass_expr :
            return ExprKind.assignment
        if k == while_statement :
            return LoopKind.while_loop
        if k == do_while_statement :
            return LoopKind.do_while_loop
        if k == for_statement :
            return LoopKind.for_loop
        else :
            return None

def _get_variables(declarations, kind) :
    
    v = []
    for d in declarations :
        if d.type in fun_expr :
            v.append(Function(d))
        else :
            v.append(_parse_variable(d,kind))
    if v != [] :
        return v

def _parse_expr(src) :
    kind = _get_kind(src.type)
    if kind == ExprKind.update :
        first = src.argument.name
        second = None
    else :
        if src.left.value is None :
            first = src.left.name
            second = src.right.value
        else :
            first = src.right.name
            second = src.left.value
    
    return Expression(kind,src.operator,first,second)

def _parse_conditional(src) :
    condition = _parse_expr(src.test)
    if_block = parse(src.consequent.body)
    else_block = parse(src.alternate.body)

    return Conditional(condition,if_block,else_block)

def for_to_while(src) :
    increment = _parse_expr(src.update)
    body = parse(src.body.body)
    test = _parse_expr(src.test)
    body.append(increment)
    loop = Loop(LoopKind.while_loop,test,body)
    init =  _get_variables(src.init.declarations,src.kind)
    init.append(loop)
    return init

def _parse_loop(src) :
    kind = _get_kind(src.type)
    if kind == LoopKind.for_loop :
        return for_to_while(src)
    else :
        test = _parse_expr(src.test)
        body = parse(src.body.body)
        return [Loop(kind,test,body)]
    
def is_variable(element) :
    return element.type == var

def is_function(element) :
    return  element.type == fun_declaration

def is_conditional(element) :
    return element.type == cond_expr

def is_expression(element) :
    return element.type == expr

def is_loop(element) :
    return element.type == for_statement or \
            element.type == while_statement or \
            element.type == do_while_statement

def parse(src) :

    body = []
    for e in src :
        if is_function(e) :
            body.append(Function(e))
        if is_variable(e) :
            body += _get_variables(e.declarations,e.kind)
        if is_conditional(e) :
            body.append(_parse_conditional(e))
        if is_expression(e) :
            body.append(_parse_expr(e.expression))
        if is_loop(e) :
            body += _parse_loop(e)
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