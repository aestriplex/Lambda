# TODO: 
# (1) make Context done
# (2) implement array theory
# (3) implement async functions theory

import esprima
from enum import Enum
from abc import ABC, abstractmethod
from z3 import Int, Real, Bool
from sys import getsizeof
import time

class Exe(ABC) :

    @abstractmethod
    def _get_constraints(self) : ...

class Language(Enum) :
    Javascript = 0x00

class Body() :

    def __init__(self, lst: list) -> None :
        self._content = lst

    def __str__(self) -> str :
        pass

    def _build_body_repr(self, body: list, s: str) -> str:
        pass
    
    def remove_first(self) -> None :
        del self._content[0]

    def remove_last(self) -> None :
        del self._content[-1]

    def get_list(self) -> list :
        return self._content

class Array(Exe) :

    def _get_constraints(self) : ...

class Object(Exe) :

    def _get_constraints(self) : ...

class BaseType(Exe) :

    def _get_constraints(self) : ...

class Call(Exe) :

    def __init__(self,callee,params) :
        self._callee = callee
        self._params = params

    def __str__(self) :
        return f"<CALL {self._callee}>"

    def _get_constraints(self) : ...

class Conditional(Exe) :

    def __init__(self,test,if_block,else_block) :
        self.test = test
        self.first = if_block
        self.second = else_block

    def __str__(self) :
        return f"<Conditional>"

    def _get_constraints(self) : ...

class Iteration(Exe) :

    def __init__(self,kind,test,body) :
        self.kind = kind
        self.test = test
        self.body = body
    
    def __str__(self) :
        return f"<Loop: {self.kind}>"

    def _get_constraints(self) : ...

class Fun(Exe) :

    def __init__(self,name,params,body,isasync) :
        self._name = name
        self._params = params
        self._body = body
        self._async = isasync

    def __str__(self) :
        return f"<FUN: {self._name}>"

    def _get_constraints(self) : ...

class Variable(Exe) :

    def __init__(self,name,kind,value = None) :

        if type(name) != str :
            raise VarTypeException(name)

        self._name = name
        self._kind = kind
        self._value = value

        # if type(self._value) == int :
        #     self._val = Int(self._name)
        # elif type(self._value) == float :
        #     self._val = Real(self._name)

        # if self._value is not None :
        #     self._constraints = [self._val == self._value]

    def __str__(self) :
        return f"<VAR: {self._name}>"

    def _get_constraints(self) : ...

class Expression(Exe) :

    def __init__(self,kind,operator,first,second) :
        self.kind = kind
        self.operator = operator
        self.first = first
        self.second = second
        #self._get_constraints()

    def __str__(self) :
        return f"<Expr: ({self.operator})>"

    def _get_constraints(self) : ...
    
    # def _get_constraints(self) :
    #     if self.kind == ExprKind.assignment and self.operator == "=" :
    #         lbls = self._get_labels()
    #         self._val = self._get_vars(lbls)
    #         ctx.add(self.first)
    #         if type(self.second) == str :
    #             ctx.add(self.second)
    #             self._constraints = [self._val[0] == self._val[1]]
    #         else :
    #             self._constraints = [self._val[0] == self.second]
    #     elif self.kind == ExprKind.binary :
    #         self._val = []
    #         lbls = self._get_labels()
    #         self._val.append(ctx.get_var(lbls[0]))
    #         self._val.append(ctx.get_var(lbls[1]))
    #         self._constraints = [self._get_binary_expr()]
    #     else :
    #         lbl_1 = f"{self.first}{ctx.next(self.first)}"
    #         ctx.add(self.first)
    #         lbl_2 = f"{self.first}{ctx.next(self.first)}"
    #         ctx.add(self.first)
    #         self._val = self._get_vars([lbl_1,lbl_2])
    #         self._constraints = [self._val[0] == self._get_update(self._val[1])]

    # def _get_labels(self) :
    #     lbls = []
    #     f_index = ctx.get_index(self.first)
    #     s_index = ctx.get_index(self.second)

    #     if f_index is not None :
    #         lbls.append(f"{self.first}{f_index}")
    #         # if f_index > 1 :
    #         #     lbls.append(f"{self.first}{f_index}")
    #         # else :
    #         #     lbls.append(f"{self.first}")
    #     if s_index is not None :
    #         lbls.append(f"{self.second}{s_index}")
    #         # if s_index > 1 :
    #         #     lbls.append(f"{self.second}{s_index}")
    #         # else :
    #         #     lbls.append(f"{self.second}")
    #     return lbls
    
    # def _get_vars(self,labels) :
    #     val = []
    #     for lbl in labels :
    #         if type(self.second) == int :
    #             val.append(Int(lbl))
    #         elif type(self.second) == float :
    #             val.append(Real(lbl))
    #         elif type(self.second) == bool :
    #             val.append(Bool(lbl))
    #         else :
    #             raise UnsupportedTypeException(type(self.second))
    #     return val

    # def _get_binary_expr(self) :
    #     switch = {
    #         "==": self._val[0] == self._val[1],
    #         "===": self._val[0] == self._val[1],
    #         "!=": self._val[0] != self._val[1],
    #         "!==": self._val[0] != self._val[1],
    #     }
    #     if self.operator not in switch :
    #         raise UnsupportedOperatorException(self.operator)
    #     return switch.get(self.operator)

    # def _get_operator(self) :
    #     l = len(self.operator)
    #     return self.operator[:l-1]
    
    # def _get_update(self,var) :
    #     o = self._get_operator()
    #     switch = {
    #         "+": lambda x: x + self.second,
    #         "-": lambda x: x - self.second,
    #         "*": lambda x: x * self.second,
    #         "/": lambda x: x / self.second,
    #         "**": lambda x: x ** self.second,
    #         "%": lambda x: x % self.second,
    #     }
    #     if o not in switch :
    #         raise UnsupportedOperatorException(self.operator)
    #     return switch.get(o)(var)

class Context() :
    
    def __init__(self) :
        self._occurrencies = {}
        self._vars = []
        self._types = {}

    def __src__(self) :
        return f"<Context (size {getsizeof(self)})>"

    def add(self,occurrence) :
        if occurrence in self._occurrencies :
            self._occurrencies[occurrence] += 1
        else :
            self._occurrencies.update({occurrence : 1})

    def get_index(self, name) :
        if type(name) is str :
            if name in self._occurrencies :
                return self._occurrencies[name]
            return 0
        return None

    def next(self,name) :
        if name in self._occurrencies:
            return self._occurrencies[name] + 1
        return None
    
    def add_var(self,var) :
        if type(var) == list :
            self._vars += var
        else :
            self._vars.append(var)
    
    def get_var(self,name) :
        for v in self._vars :
            if str(v) == name :
                return v
        return None

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

class DepthTypeException(Exception) :
    
    def __init__(self,_t) :
        super().__init__(f"Depth must be an integer, not {_t.__name__}.")

class BodyTypeException(Exception) :
    
    def __init__(self,_t) :
        super().__init__(f"Depth must be a list, not {_t.__name__}.")

class ScriptTypeException(Exception) :
    
    def __init__(self,_t) :
        super().__init__(f"Script parameter must be an esprima.nodes.Script, not {_t.__name__}.")

class VarTypeException(Exception) :
    
    def __init__(self,_t) :
        super().__init__(f"You must pass a string for parameter {_t.__name__} insted of {type(_t).__name__}.")

class KindTypeException(Exception) :
    
    def __init__(self) :
        super().__init__(f"Kind unknown.")

class TypeException(Exception) :

    def __init__(self,_t) :
        super().__init__(f"{_t.__name__} must inherits from `Instruction`.")

class UnsupportedOperatorException(Exception) :

    def __init__(self,o) :
        super().__init__(f"{o} is not supported.")
    
class UnsupportedTypeException(Exception) :

    def __init__(self,_t) :
        super().__init__(f"Type {_t} is not supported.")

class InnerContextMissingException(Exception) :

    def __init__(self) :
        super().__init__("In order to process binary expression, you have to specify an inner context (default none).")

class VariableMissingException(Exception) :

    def __init__(self,_n) :
        super().__init__(f"Variable {_n} must be delacred in the context.")
    
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
    identifier = "Identifier"
    obj = "ObjectExpression"
    array = "ArrayExpression"

class Parser :

    def __init__(self, source) -> None :
        self._result = self._parse_block(source.body)

    def result(self) -> list : 
        return Body(self._result)

    def _parse_block_variable(self, src, kind) :
        kind = self._get_kind(kind)
        name = src.id.name
        value = self._get_var_value(src)
        return Variable(name,kind,value)    

    def _get_var_value(self, src) :
        if src.init.type == VarType.literal :
            return src.init.value
        if src.init.type == VarType.obj :
            return self._parse_block_object(src.init.properties)
        if src.init.type == VarType.array :
            return self._parse_block_array(src.init.elements)

    def _parse_block_object(self, prop) :
        obj = {}
        for p in prop :
            if p.key.type == VarType.identifier :
                obj.update({p.key.name : p.value.value})
            else :
                obj.update({p.key.value : p.value.value})
        return obj

    def _parse_block_array(self, elements) :
        return [e.value for e in elements]

    def _parse_block_call(self, src) :
        callee = src.callee.name
        params = [a.value for a in src.arguments]
        return Call(callee,params)

    def _get_kind(self, k) :
        if k == "var" :
            return VarKind.var
        if k == "const" :
            return VarKind.const
        if k == EsprimaTypes.bin_expr :
            return ExprKind.binary
        if k == EsprimaTypes.up_expr :
            return ExprKind.update
        if k == EsprimaTypes.ass_expr :
            return ExprKind.assignment
        if k == EsprimaTypes.while_statement :
            return LoopKind.while_loop
        if k == EsprimaTypes.do_while_statement :
            return LoopKind.do_while_loop
        if k == EsprimaTypes.for_statement :
            return LoopKind.for_loop
        else :
            raise KindTypeException()

    def _get_variables(self, declarations, kind) :
        v = []
        for d in declarations :
            if d.init is not None :
                if d.init.type in EsprimaTypes.fun_expr :
                    d.init.id = d.id
                    v.append(self._parse_block_fun(d.init))
                else :
                    v.append(self._parse_block_variable(d,kind))
        return v

    def _parse_block_expr(self, src) :
        kind = self._get_kind(src.type)
        if kind == ExprKind.update :
            first = src.argument.name
            if src.operator == "++" :
                embedded_operator = "+"
            elif src.operator == "--" :
                embedded_operator = "-"
            operator = "="
            second = Expression(ExprKind.update,embedded_operator,first,1)
            kind = ExprKind.assignment
        else :
            if src.left.name is not None and src.right.name is not None :
                first = src.left.name
                second = src.right.name
            elif src.left.name is not None and src.right.name is None :
                first = src.left.name
                second = src.right.value
            elif src.left.name is None and src.right.name is not None :
                first = src.right.name
                second = src.left.value
            else :
                first = src.right.value
                second = src.left.value
            operator = src.operator
        
        return Expression(kind,operator,first,second)

    def _parse_block_fun(self, src) :
        name = src.id.name
        params = [Variable(p.name,"var") for p in src.params]
        body = self._parse_block(src.body.body)
        return Fun(name,params,body,src.isAsync)

    def _parse_block_conditional(self, src) :
        condition = self._parse_block_expr(src.test)
        if src.consequent.body is None :
            if_block = self._parse_block([src.consequent])
        else :
            if_block = self._parse_block(src.consequent.body)
        if src.alternate is not None :
            if src.alternate.body is None:
                else_block = self._parse_block([src.alternate])
            else :
                else_block = self._parse_block(src.alternate.body)
        else :
            else_block = None

        return Conditional(condition,if_block,else_block)

    def _for_to_while(self, src) :
        increment = self._parse_block_expr(src.update)
        body = self._parse_block(src.body.body)
        test = self._parse_block_expr(src.test)
        body.append(increment)
        loop = Iteration(LoopKind.while_loop,test,body)
        init =  self._get_variables(src.init.declarations,src.kind)
        init.append(loop)
        return init

    def _parse_block_loop(self, src) :
        kind = self._get_kind(src.type)
        if kind == LoopKind.for_loop :
            return self._for_to_while(src)
        else :
            test = self._parse_block_expr(src.test)
            body = self._parse_block(src.body.body)
            return [Iteration(kind,test,body)]
        
    def _is_variable(self, element) :
        return element.type == EsprimaTypes.var

    def _is_function(self, element) :
        return  element.type == EsprimaTypes.fun_declaration

    def _is_conditional(self, element) :
        return element.type == EsprimaTypes.cond_expr

    def _is_expression(self, element) :
        return element.type == EsprimaTypes.expr

    def _is_loop(self, element) :
        return element.type == EsprimaTypes.for_statement or \
                element.type == EsprimaTypes.while_statement or \
                element.type == EsprimaTypes.do_while_statement
            
    def _is_call(self, element) :
        return element.type == EsprimaTypes.expr and \
                element.expression.type == EsprimaTypes.call

    def _parse_block(self, src) :
        body = []
        for e in src :
            if self._is_function(e) :
                body.append(self._parse_block_fun(e))
            elif self._is_variable(e) :
                body += self._get_variables(e.declarations,e.kind)
            elif self._is_conditional(e) :
                body.append(self._parse_block_conditional(e))
            elif self._is_call(e) :
                body.append(self._parse_block_call(e.expression))
            elif self._is_expression(e) :
                body.append(self._parse_block_expr(e.expression))
            elif self._is_loop(e) :
                body += self._parse_block_loop(e)
        return body

start = time.time()
with open(r"C:\Users\mnicoli\Documents\GitHub\Lambda\src\test.js","r") as f :
    aaa = f.read()
try :
    source = esprima.parseScript(aaa)
except Exception as ex:
    print(f"ERROR: {ex}")
    exit()

print(source.body)
parser = Parser(source)
l = parser.result()
print(*l.get_list())
stop = time.time()
print(f"Time: {stop-start}")
print("*** END ***")