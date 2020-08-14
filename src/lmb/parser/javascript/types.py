from enum import Enum

class EsprimaTypes() :
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
    array = "ArrayExpression"