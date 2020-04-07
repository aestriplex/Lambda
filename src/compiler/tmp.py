# TODO: 
# (1) make Context done
# (2) implement array theory
# (3) implement async functions theory

import esprima
from enum import Enum
from abc import ABC, abstractmethod
from z3 import Int, Real
import time

var = "VariableDeclaration"
expr = "ExpressionStatement"
call = "CallExpression"
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

occ = {}
assertions = []

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

class KindTypeException(Exception) :
    
    def __init__(self) :
        self.msg = f"Kind unknown"
    
    def __str__(self) :
        return self.msg

class TypeException(Exception) :

    def __init__(self,_t) :
        self.msg = f"{_t.__name__} must inherits from `Instruction`"
    
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

class Exe(ABC) :

    @abstractmethod
    def to_ssa(self) :
        pass

class Expression(Exe) :

    def __init__(self,kind,operator,first,second = None) :
        self.kind = kind
        self.operator = operator
        self.first = first
        self.second = second

    def __str__(self) :
        return f"<Expr: {self.operator}>"
    
    def to_ssa(self) :
        pass

class Call(Exe) :

    def __init__(self,callee,params) :
        self._callee = callee
        self._params = params

    def __str__(self) :
        return f"<CALL {self._callee}>"

    def to_ssa(self) :
        pass

class Conditional(Exe) :

    def __init__(self,test,if_block,else_block) :
        self.test = test
        self.first = if_block
        self.second = else_block

    def __str__(self) :
        return f"<Conditional>"
    
    def to_ssa(self) :
        pass

class Iteration(Exe) :

    def __init__(self,kind,test,body) :
        self.kind = kind
        self.test = test
        self.body = body
    
    def __str__(self) :
        return f"<Loop: {self.kind}>"
    
    def to_ssa(self) :
        pass

class Fun(Exe) :

    def __init__(self,name,params,body,isasync) :
        self._name = name
        self._params = params
        self._body = body
        self._async = isasync

    def __str__(self) :
        return f"<FUN: {self._name}>"
    
    def to_ssa(self) :
        pass

class Variable(Exe) :

    def __init__(self,name,kind,value = None) :
        if type(name) != str :
            raise VarTypeException(name)

        self._name = name
        self._kind = kind
        self._value = value
    
    def __str__(self) :
        return f"<VAR: {self._name}>"
    
    def to_ssa(self) :
        if type(self._value) == int :
            val = Int(self._name)
        elif type(self._value) == float :
            val = Real(self._name)
        if self._name not in occ :
            occ.update({self._name : [val]})
        else :
            pass
        i = len(occ[self._name])
        if self._value is not None :
            assertions.append(occ[self._name][i-1] == self._value)

class Context :
    
    def __init__(self) :
        self._occurrencies = {}
        self._assertions = []

    def __src__(self) :
        return f""

    def add(self,occurrence) :
        pass

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

def _parse_call(src) :
    callee = src.callee.name
    params = [a.value for a in src.arguments]
    return Call(callee,params)

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
        raise KindTypeException()

def _get_variables(declarations, kind) :
    
    v = []
    for d in declarations :
        if d.init.type in fun_expr :
            d.init.id = d.id
            v.append(_parse_fun(d.init))
        else :
            v.append(_parse_variable(d,kind))

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

def _parse_fun(src) :
    name = src.id.name
    params = [Variable(p.name,"var") for p in src.params]
    body = parse(src.body.body)
    return Fun(name,params,body,src.isAsync)

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
    loop = Iteration(LoopKind.while_loop,test,body)
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
        return [Iteration(kind,test,body)]
    
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
        
def is_call(element) :
    return element.type == expr and \
            element.expression.type == call

def parse(src) :

    body = []
    for e in src :
        if is_function(e) :
            body.append(_parse_fun(e))
        elif is_variable(e) :
            body += _get_variables(e.declarations,e.kind)
        elif is_conditional(e) :
            body.append(_parse_conditional(e))
        elif is_call(e) :
            body.append(_parse_call(e.expression))
        elif is_expression(e) :
            body.append(_parse_expr(e.expression))
        elif is_loop(e) :
            body += _parse_loop(e)
    return body

start = time.time()
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
for e in l :
    e.to_ssa()
stop = time.time()
print(f"Time: {stop-start}")
print("*** END ***")