import esprima
from struct import *
from types import *
from exceptions import KindTypeException

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