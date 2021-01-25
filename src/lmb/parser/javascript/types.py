from enum import Enum

class EsprimaTypes() :
    var = "VariableDeclaration"
    expr = "ExpressionStatement"
    call = "CallExpression"
    up_expr = "UpdateExpression"
    bin_expr = "BinaryExpression"
    member = "MemberExpression"
    ass_expr = "AssignmentExpression"
    cond_expr = "IfStatement"
    for_statement = "ForStatement"
    while_statement = "WhileStatement"
    do_while_statement = "DoWhileStatement"
    fun_declaration = "FunctionDeclaration"
    generic_expression = ["UpdateExpression", "AssignmentExpression", "BinaryExpression"]
    fun_expr = ["FunctionExpression","ArrowFunctionExpression"]
    declarator = ["VariableDeclarator","ObjectDeclarator"]

update_operators = ["+=", "-=", "*=", "/=", "&=", "|="]
    
class VarKind(Enum) :
    var = 0
    const = 1

class LoopKind(Enum) :
    for_loop = 0
    while_loop = 1
    do_while_loop = 2

class CallType :
    identifier = "Identifier"
    member = "MemberExpression"
    
class VarType :
    literal = "Literal"
    identifier = "Identifier"
    obj = "ObjectExpression"
    array = "ArrayExpression"
    new = "NewExpression"