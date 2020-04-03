import esprima
from .exceptions import ScriptTypeException
from .struct import Variable


var = "VariableDeclaration"
fun = ["FunctionDeclaration", "FunctionExpression","ArrowFunctionExpression"]
declarator = ["VariableDeclarator","ObjectDeclarator"]


def print_body(body) :

    for e in body :
        yield type(e).__name__ 


def _parse_variable(declarations, kind) :

    for d in declarations :
        yield Variable(d,kind)

def parse(src) :
        
    if type(src) != esprima.nodes.Script :
        raise ScriptTypeException(type(src))

    body = []
    for e in src :
        if e.type == Parser.var :
            body.append(Parser._parse_variable(e.declarations,e.kind))

    return body