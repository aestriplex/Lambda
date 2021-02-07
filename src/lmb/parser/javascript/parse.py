import esprima
import time
from typing import Generator, Any
from lmb.structures import Call, Expression, Conditional, Iteration, Fun, Variable, Body, Array, Object, Value, undefined, Pointer, addr_map
from .types import EsprimaTypes, VarKind, VarType, LoopKind, update_operators, CallType, StdObjects
from lmb.options import ExprKind, Types
from lmb.exceptions import KindTypeException

class Parser :
    """
    """
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
        value = self._get_var_value(src, kind, name)
        return Variable(name,kind,value)

    def _get_var_value(self, src: esprima.nodes, kind: Any, name: str) :
        if src.init is None or src.init.name == StdObjects.undefined :
            return Variable(name, kind, Value(src.id.name, undefined()))
        if src.init.type == VarType.literal :
            if src.init.raw == StdObjects.null :
                return Pointer(hex(0),src.id.name)
            else :
                return Variable(name, kind, Value(src.id.name, src.init.value))
        if src.init.type == VarType.obj :
            value = self._parse_block_object(src.init.properties)
            addr = addr_map.add(Object(None,value))
        if src.init.type == VarType.array :
            value = self._parse_block_array(src.init.elements)
            addr = addr_map.add(Array(None,value))
        return Pointer(addr,src.id.name)

    def _parse_block_object(self, prop: esprima.nodes) -> dict :
        obj = {}
        for p in prop :
            key_type, value_type = p.key.type, p.value.type
            
            if key_type == VarType.identifier :
                key = p.key.name
            else :
                key = p.key.value

            if value_type == VarType.literal :
                obj.update({key : Value(None, p.value.value)})
            elif value_type == VarType.array :
                val = self._parse_block_array(p.value.elements)
                obj.update({key : Array(key,val)})
            elif value_type == VarType.obj :
                val = self._parse_block_object(p.value.properties)
                obj.update({key : Object(key,val)})
            
        return obj

    def _parse_block_array(self, elements) -> list :
        ar = []
        for e in elements :
            if e.type == VarType.literal :
                ar.append(Value(None, e.value))
            elif e.type == VarType.array :
                val = self._parse_block_array(e.elements)
                ar.append(Array(None, val))
            elif e.type == VarType.obj :
                val = self._parse_block_object(e.properties)
                ar.append(Object(None,val))
        return ar

    def _parse_block_call(self, src) :
        callee = src.callee.name
        params = [a.value for a in src.arguments]
        return Call(callee,params)

    def _get_kind(self, k: str) -> Any :
        if k == "var" :
            return VarKind.var
        if k == "const" :
            return VarKind.const
        if k == VarType.identifier:
            return ExprKind.binary
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
        if k == EsprimaTypes.unary_expr :
            return ExprKind.unary
        else :
            raise KindTypeException()

    def _get_variables(self, declarations, kind) :
        v = []
        for d in declarations :
            # if d.init is not None :
            if d.init is not None and d.init.type in EsprimaTypes.fun_expr :
                d.init.id = d.id
                v.append(self._parse_block_fun(d.init))
            else :
                v.append(self._parse_block_variable(d,kind))
            # else :
            #     v.append(Variable(d.id.name,VarKind.var,Types.undefined))
        return v
    
    def _get_call_name(self, obj: str, member: str) :
        return f"{obj}.{member}"

    def _get_arr_name(self, obj: str, index: str) :
        return f"{obj}[{index}]"
    
    def _get_expr_components(self, left: object, right: object) -> tuple :
        if left.name is not None and right.name is not None :
            first = Variable(left.name)
            second = Variable(right.name)
        elif left.name is not None and right.name is None :
            first = Variable(left.name)
            if right.type == VarType.literal :
                second = Value(None, right.value)
            elif right.type in EsprimaTypes.generic_expression :
                second = self._parse_block_expr(right)
        elif left.name is None and right.name is not None :
            first = Variable(right.name)
            second = Value(None, left.value)
        elif left.type == CallType.member and right.type == VarType.literal :
            if left.computed is True :
                first = Variable(self._get_arr_name(left.object.name,left.property.value))
            else :
                first = Variable(self._get_call_name(left.object.name,left.property.name))
            second = Value(None,right.value)
        else :
            first = Value(None, right.value)
            second = Value(None, left.value)
        
        return first, second

    def _check_null(self, src: dict) -> Any :
        operator = "&&"
        first = Expression(ExprKind.binary,"!=",Variable(src.name),Value(src.name,undefined()))
        second = Expression(ExprKind.binary,"!=",Variable(src.name),Pointer(hex(0),src.name))
        return first, second, operator

    def _case_undefined(self, src: dict) -> Any :
        if src.left.name == StdObjects.undefined :
            first = Value(None,undefined())
        else :
            first = Variable(src.left.name)
        if src.right.name == StdObjects.undefined :
            second = Value(None,undefined())
        else :
            pass
        return first, second, src.operator

    def _case_null(self, src: dict) -> Any :
        if src.left.raw == StdObjects.null :
            first = Pointer(hex(0),src.left.raw)
        else :
            first = Variable(src.left.name)
        if src.right.raw == StdObjects.null :
            second = Pointer(hex(0),src.right.raw)
        else :
            pass
        return first, second, src.operator

    def _parse_block_expr(self, src: esprima.nodes) -> Expression :
        kind = self._get_kind(src.type)
        if src.operator in update_operators :
            operator = "="
            first = Variable(src.left.name)
            if src.right.type in EsprimaTypes.generic_expression :
                embedded_second = self._parse_block_expr(src.right)
            else :
                if src.right.value is None :
                    embedded_second = Value(src.right.value)
                else :
                    embedded_second = Variable(src.right.name)
            second = Expression(ExprKind.binary,
                                src.operator[0],
                                Variable(src.left.name),
                                embedded_second)
            kind = ExprKind.assignment
        elif kind == ExprKind.update :
            first = Variable(src.argument.name)
            if src.operator == "++" :
                embedded_operator = "+"
            elif src.operator == "--" :
                embedded_operator = "-"
            operator = "="
            second = Expression(ExprKind.binary,
                                embedded_operator,
                                Variable(src.argument.name),
                                Value(None,1))
            kind = ExprKind.assignment
        elif kind == ExprKind.assignment :
            first, second = self._get_expr_components(src.left, src.right)
            operator = src.operator
        elif kind == ExprKind.binary :
            if src.right is None and src.left is None :
                first, second, operator = self._check_null(src)
            elif src.right.type == EsprimaTypes.bin_expr and \
                src.left.type == EsprimaTypes.bin_expr :
                operator = src.operator
                first = self._parse_block_expr(src.left)
                second = self._parse_block_expr(src.right)
            elif src.right.type == EsprimaTypes.bin_expr :
                first = self._parse_block_expr(src.right)
                operator = src.operator
                if src.left.name is None :
                    second = Value(None, src.left.value)
                else :
                    second = Variable(src.left.name)
            elif src.left.type == EsprimaTypes.bin_expr :
                if src.right.name is None :
                    first = Value(None, src.right.value)
                else :
                    first = Variable(src.right.name)
                second = self._parse_block_expr(src.left)
                operator = src.operator
            else:
                if src.left.name == StdObjects.undefined or \
                   src.right.name == StdObjects.undefined :
                    first, second, operator = self._case_undefined(src)
                elif src.left.raw == StdObjects.null or \
                     src.right.raw == StdObjects.null :
                    first, second, operator = self._case_null(src)
                else :
                    first, second = self._get_expr_components(src.left, src.right)
                    operator = src.operator
        elif kind == ExprKind.unary :
            if src.argument.type == VarType.identifier :
                # first, second, operator = self._check_null(src.argument)
                second = None
                operator = "!"
                first = self._parse_block_expr(src.argument)
            else :
                pass
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