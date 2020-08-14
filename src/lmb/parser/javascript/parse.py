import esprima
import time
from lmb.structures import Call, Expression, Conditional, Iteration, Fun, Variable, Body
from .types import EsprimaTypes, VarKind, ExprKind, VarType, LoopKind
from lmb.exceptions import KindTypeException

class Parser :

    def __init__(self, source: str, stats: bool = False) -> None :
        if stats :
            self._start_time = time.time()

        self._source = esprima.parseScript(source)
        self._result = self._parse_block(self._source.body)

        if stats :
            self._end_time = time.time()
            self._stats = self._end_time - self._start_time

    def result(self) -> list : 
        return Body(self._result)
    
    def stats(self) :
        return self._stats

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