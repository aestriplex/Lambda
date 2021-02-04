from enum import Enum

class EsprimaTypes() :
    null = "null"
    var = "VariableDeclaration"
    expr = "ExpressionStatement"
    call = "CallExpression"
    up_expr = "UpdateExpression"
    bin_expr = "BinaryExpression"
    unary_expr = "UnaryExpression"
    member = "MemberExpression"
    ass_expr = "AssignmentExpression"
    cond_expr = "IfStatement"
    for_statement = "ForStatement"
    while_statement = "WhileStatement"
    do_while_statement = "DoWhileStatement"
    fun_declaration = "FunctionDeclaration"
    generic_expression = ["UpdateExpression", "AssignmentExpression", "BinaryExpression", "UnaryExpression"]
    fun_expr = ["FunctionExpression","ArrowFunctionExpression"]
    declarator = ["VariableDeclarator","ObjectDeclarator"]

update_operators = ["+=", "-=", "*=", "/=", "&=", "|="]
    
class VarKind(Enum) :
    var   = 0x00
    const = 0x01

class LoopKind(Enum) :
    for_loop      = 0x00
    while_loop    = 0x01
    do_while_loop = 0x02

class CallType :
    identifier = "Identifier"
    member = "MemberExpression"
    
class VarType :
    literal = "Literal"
    identifier = "Identifier"
    obj = "ObjectExpression"
    array = "ArrayExpression"
    new = "NewExpression"