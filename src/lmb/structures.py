from __future__ import annotations
import re
from enum import Enum
from abc import ABC, abstractmethod
from .exceptions import VarTypeException, UnsupportedTypeException, BaseTypeException, InconsistentTypeExpression
from .context import Context, Label
from .utils import remove_ctx_index, remove_var_name
from .options import ExprKind, Types
from .memory_map import MemoryMap
from typing import Any, Generator
from z3 import z3, And, Or, Not, If, Int, Real, String, IntVal, RealVal, StringVal, ExprRef, BoolRef, Datatype, Const

_ANONYMOUS = "Anonymous"
GlobalType = None
addr_map = MemoryMap()

def set_global_datatypes() :
    global GlobalType
    GlobalType = Datatype('GlobalType')
    GlobalType.declare('undefined')
    GlobalType.declare('null')
    GlobalType = GlobalType.create()

def get_z3_value(value: object) -> z3 :
    if type(value) == int :
        return IntVal(value)
    elif type(value) == float :
        return RealVal(value)
    elif type(value) == str :
        return StringVal(value)
    elif type(value) == undefined :
        return GlobalType.undefined

def get_z3_type(name: str, t: object) -> z3 :
    if t == int :
        return Int(name)
    elif t == float :
        return Real(name)
    elif t == str :
        return String(name)
    elif t == undefined :
        return Const(name,GlobalType)
    elif t == null :
        return Const(name,GlobalType)

class BlockType(Enum) :
    generic = 0x00
    if_block = 0x01
    else_block = 0x02

class Exe(ABC) :

    @abstractmethod
    def get_constraints(self, ctx: Context = None) -> list : ...

    @abstractmethod
    def to_ssa(self, ctx: Context, parent_label: str = None) : ...

class undefined : 

    def __init__(self) :
        self._type = "undefined"

    def __str__(self) :
        return "undefined"

class null :

    def __init__(self) :
        self._type = "null"

    def __str__(self) :
        return "null"

    # def get_constraints(self, ctx: Context = None) -> list :
    #     return self._constraints

    # def to_ssa(self, ctx: Context, parent_label: str = None) :
    #     ctx.add(parent_label,type(self))
    #     lbl = ctx.get_label(parent_label,Label.prev)
    #     self._constraints.append(Const(lbl, GlobalType) == GlobalType.null)

class Body() :

    def __init__(self, lst: list, ctx: Context = None) -> None :
        self._content = lst
        if ctx is None :
            self._global_context = Context()
        else :
            self._global_context = ctx

    def __str__(self) -> str :
        var = "var" if len(self._content) == 1 else "vars"
        return f"<BODY ({len(self._content)} {var})>"

    def __repr__(self) -> str :
        var = "var" if len(self._content) == 1 else "vars"
        return f"<BODY ({len(self._content)} {var}) at {hex(id(self))}>"

    def __iadd__(self, other: list) -> self :
        if type(other) != list :
            raise UnsupportedTypeException(type(other))
        self._content += other
        return self

    def get_context(self) -> Context :
        return self._global_context

    def _get_body_repr(self, body: list, s: str) -> str:
        pass

    def add_element(self, e: Exe) -> None :
        self._content.append(e)
    
    def add_list(self, l: list) -> None :
        self._content += l
    
    def remove_first(self) -> None :
        del self._content[0]

    def remove_last(self) -> None :
        del self._content[-1]

    def get_list(self) -> list :
        return self._content
    
    def build_body(self) -> None :
        for e in self._content :
            if type(e) != Call :
                e.to_ssa(self._global_context)

class Block(Exe) :

    def __init__(self, 
                 body: list, 
                 block_type: BlockType = BlockType.generic, 
                 parent_ctx: Context = None) -> None :
        self._body = body
        self._modified = None
        self._constraints = []
        self._b_type = block_type
        if parent_ctx is not None :
            self._ctx = Context(parent_ctx)
        else :
            self._ctx = None
    
    def get_body(self) -> list :
        return self._body

    def get_context(self) -> Context :
        return self._ctx
    
    def get_modified(self) -> dict :
        return self._modified
    
    def get_constraints(self, ctx: Context = None) -> list : 
        return self._constraints
    
    def add_constraints(self, constraints: list) -> None :
        self._constraints += constraints

    def to_ssa(self, ctx: Context, parent_label: str = None) : 
        if self._ctx is None :
            self._ctx = Context(ctx)
        else :
            self._ctx = ctx
        
        if self._body is not None :
            for e in self._body :
                if type(e) != Call :
                    e.to_ssa(self._ctx)

            for e in self._body :
                self._constraints += e.get_constraints()

        # self._modified = self._ctx.get_last_update_vars()
        self._modified = self._ctx.get_occurrencies()

class Pointer(Exe) :

    def __init__(self, addr: str, label: str) -> None :
        self._addr = addr
        self._label = label
        self._constraints = [] # only used in case of null

    def __str__(self) -> str :
        return f"<{addr_map.get(self._addr)} at {self._addr}>"

    def __repr__(self) -> str :
        return f"<Pointer {self._addr} at ({hex(id(self))})>"

    def get_addr(self) -> str :
        return self._addr

    def get_value(self) -> Any:
        return addr_map.get(self._addr)

    def get_constraints(self, ctx: Context = None) -> list :
        val = addr_map.get(self._addr)
        if val is not None :
            return addr_map.get(self._addr).get_constraints(ctx)
        return self._constraints
    
    def to_ssa(self, ctx: Context, parent_label: str = None) -> None :
        value = addr_map.get(self._addr)
        if value is not None :
            value.to_ssa(ctx,self._label)
        else :
            ctx.add(self._label,type(null()))
            lbl = ctx.get_label(self._label,Label.prev) 
            self._constraints.append(Const(lbl, GlobalType) == GlobalType.null)

class Array(Exe) :

    def __init__(self, name: str, content: list) -> None :
        self._name = _ANONYMOUS if name is None else name
        self._content = content
        self._constraints = []

    def __str__(self) -> str :
        return f"<Array {self._name}>"

    def __repr__(self) -> str :
        return f"<Array {self._name} at {hex(id(self))}>"

    def get_name(self) -> str :
        return self._name

    def _clean_label(self, label: str) -> str :
        return re.sub(remove_ctx_index,"",label)

    def _find_label(self, ctx: Context, val: Exe, i: int, parent_label: str) -> str :
        if self._name == _ANONYMOUS :
            lbl = f"[{i}]"
        else :
            lbl = f"{self._name}[{i}]"
        if parent_label is not None :
            lbl = f"{self._clean_label(parent_label)}{lbl}"
        ctx.add(lbl, val.get_type())
        return ctx.get_label(lbl,Label.prev)

    def get_constraints(self, ctx: Context = None) -> list :
        c= []
        for e in self._content :
            c += e.get_constraints()
        return c
    
    def to_ssa(self, ctx: Context, parent_label: str = None) -> None :
        i = 0
        for val in self._content :
            lbl = self._find_label(ctx, val, i, parent_label)
            i += 1
            val.to_ssa(ctx,lbl)
            
class Object(Exe) :

    def __init__(self, name: str, content: dict, is_embedded: bool = False) -> None :
        self._name = _ANONYMOUS if name is None else name
        self._content = content
        self._constraints = []

    def __str__(self) -> str :
        return f"<Obj {self._name}>"

    def __repr__(self) -> str :
        return f"<Obj {self._name} at ({hex(id(self))})>"

    def get_name(self) -> str :
        return self._name

    def _clean_label(self, label: str) -> str :
        return re.sub(remove_ctx_index,"",label)

    def _find_label(self, ctx: Context, val: Exe, key: str, parent_label: str) -> str :
        if self._name == _ANONYMOUS :
            lbl = f"{key}"
        else :
            lbl = f"{self._name}.{key}"
        if parent_label is not None :
            lbl = f"{self._clean_label(parent_label)}.{lbl}"
        ctx.add(lbl, val.get_type())
        return ctx.get_label(lbl,Label.prev)

    def get_constraints(self, ctx: Context = None) -> list :
        c= []
        for e in self._content.values() :
            c += e.get_constraints()
        return c

    def to_ssa(self, ctx: Context, parent_label: str = None) -> None :
        for key,val in zip(self._content.keys(),self._content.values()) :
            lbl = self._find_label(ctx, val, key, parent_label)
            val.to_ssa(ctx,lbl)

class Value(Exe) :

    def __init__(self, name: str, val: Any = None)  -> None :
        self._name = _ANONYMOUS if name is None else name
        self._content = val
        self._type = type(val)
        self._constraints = []

    def __str__(self) -> str :
        return f"{self._content}"

    def __repr__(self) -> str :
        return f"<Value ({type(self._content).__name__}) at {hex(id(self))}>"

    def get_name(self) -> str :
        return self._name

    def get_val(self) -> Any :
        return self._content
    
    def get_type(self) -> Any :
        return self._type

    def _find_label(self, ctx: Context) -> str :
        ctx.add(self._name, self._type)
        return ctx.get_label(self._name,Label.prev)

    def get_constraints(self, ctx: Context = None) -> list :
        return self._constraints

    def to_ssa(self, ctx: Context, parent_label: str = None) -> None :
        if parent_label is not None :
            lbl = parent_label
        else :
            lbl = self._find_label(ctx)
        if type(self._content) == int :
            self._constraints.append(Int(lbl) == self._content)
        elif type(self._content) == float :
            self._constraints.append(Real(lbl) == self._content)
        elif type(self._content) == str :
            self._constraints.append(String(lbl) == StringVal(self._content))
        elif type(self._content) == undefined :
            self._constraints.append(Const(lbl, GlobalType) == GlobalType.undefined)

class Expression(Exe) :

    def __init__(self, kind: Any, operator: Any, first: Exe, second: Exe = None) -> None :
        self._kind = kind
        self._operator = operator
        self._first = first
        self._second = second
        self._constraints = []

    def __str__(self) -> str :
        if self._second is None :
            return f"{self._operator}{self._first}"
        else :
            if type(self._first) != Expression and \
               type(self._second) != Expression :
               return f"{self._first} {self._operator} {self._second}"
            return f"({self._first} {self._operator} {self._second})"

    def __repr__(self) -> str :
        return f"<Expr {self._operator} ({self._kind.name}) at {hex(id(self))}>"

    def get_first(self) -> str :
        return str(self._first)

    def get_second(self) -> str :
        return str(self._second)

    def get_operator(self) -> str :
        return self._operator

    def _get_z3_operator(self, first: z3, second: z3, op: str) -> BoolRef :
        if op == "!" :
            return Not(first)
        elif op == "+" :   
            return first + second
        elif op == "-" :  
            return first - second
        elif op == "*" :  
            return first * second
        elif op == "/" :  
            return first / second
        elif op == "**" :  
            return first ** second
        elif op == "%" :  
            return first % second
        elif op == "==" :
            if first.sort() == GlobalType or\
                second.sort() == GlobalType :
                return first.sort() == second.sort()
            return first == second
        elif op == "!=" :
            if first.sort() == GlobalType or\
               second.sort() == GlobalType :
                return first.sort() != second.sort()
            return first != second
        elif op == "&&" :  
            return And(first,second)
        elif op == "||" :  
            return Or(first,second)
        elif op == ">" :
            return first > second
        elif op == "<" :
            return first < second
        elif op == "<=" :
            return first <= second
        elif op == ">=" :
            return first >= second
    
    def _get_compound_value(self, first: Any, second: Any, op: str) -> Any :
        if op == "!" :
            return Not(first)
        elif op == "+" :  
            return first + second
        elif op == "-" :  
            return first - second
        elif op == "*" :  
            return first * second
        elif op == "/" :  
            return first / second
        elif op == "**" :  
            return first ** second
        elif op == "%" :  
            return first % second
        elif op == "==" :
            return first == second
        elif op == "!=" :
            return first != second
        elif op == "&&" :  
            return first and second
        elif op == "||" :  
            return first or second
        elif op == ">" :
            return first > second
        elif op == "<" :
            return first < second
        elif op == "<=" :
            return first <= second
        elif op == ">=" :
            return first >= second

    def _make_constraint(self, ctx: Context, first: Any, second: Any) -> list :
        t_s = type(second)
        if t_s == Value :
            val_second = second.get_val()
            t = type(val_second)
            if t == int :
                return [Int(first) == val_second]
            elif t == float :
                return [Real(first) == val_second]
            elif t == str :
                return [String(first) == StringVal(val_second)]
        elif t_s == Variable :
            second_lbl = second.get_label()
            type_second = ctx.get_type(second_lbl)
            if type_second == int :
                return [Int(first) == Int(second_lbl)]
            elif type_second == float :
                return [Real(first) == Real(second_lbl)]
            elif type_second == str :
                return [String(first) == String(second_lbl)]
        elif t_s == Expression :
            second.to_ssa(ctx)
        else :
            t_f = ctx.get_type(first)
            f = get_z3_type(first,t_f)
            return [f == second]

    def _check_consistency(self, t1: Any, t2: Any, op: str) -> None :
        if t1 != t2 :
            if t1 != undefined and t2 != undefined and \
               (op != "==" or op != "!=") :
                raise InconsistentTypeExpression(self)

    def _get_binary_variable(self, ctx: Context, var_name: str) -> z3 :
        t_second = ctx.get_type(var_name)
        lbl_second = ctx.get_label(var_name, Label.prev)
        return get_z3_type(lbl_second, t_second)

    def get_constraints(self, ctx: Context = None) -> list :
        return self._constraints

    def to_ssa(self, ctx: Context, parent_label: str = None) -> None :
        if self._kind == ExprKind.binary :
            if type(self._first) == Expression :
                self._first.to_ssa(ctx)
                first = self._first.get_constraints(ctx)[0]
                if type(self._second) == Variable :
                    second = self._get_binary_variable(ctx,self._second.get_name())
                elif type(self._second) == Value :
                    second = get_z3_value(self._second.get_val())
                elif type(self._second) == Expression :
                    self._second.to_ssa(ctx)
                    second = self._second.get_constraints(ctx)[0]
            elif type(self._first) == Variable :
                t_first = ctx.get_type(self._first.get_name())
                lbl_first = ctx.get_label(self._first.get_name(), Label.prev)
                first = get_z3_type(lbl_first, t_first)
                if type(self._second) == Variable :
                    second = self._get_binary_variable(ctx,self._second.get_name())
                elif type(self._second) == Value :
                    t_second = type(self._second.get_val())
                    self._check_consistency(t_first,t_second,self._operator)
                    second = get_z3_value(self._second.get_val())
                elif type(self._second) == Expression :
                    self._second.to_ssa(ctx)
                    second = self._second.get_constraints(ctx)[0]
                elif type(self._second) == Pointer :
                    self._second.to_ssa(ctx)
                    second = self._second.get_constraints(ctx)[0]
            elif type(self._first) == Value :
                first = get_z3_value(self._first.get_val())
                t_first = type(self._first.get_val())
                if type(self._second) == Variable :
                    second = self._get_binary_variable(ctx,self._second.get_name())
                    self._check_consistency(t_first,t_second,self._operator)
                elif type(self._second) == Value :
                    self._check_consistency(type(self._first),type(self._second),self._operator)
                    second = get_z3_value(self._second.get_val())
                elif type(self._second) == Expression :
                    self._second.to_ssa(ctx)
                    second = self._second.get_constraints(ctx)[0]
            self._constraints.append(self._get_z3_operator(first,second,self._operator))
        elif self._kind == ExprKind.assignment :
            if type(self._second) == Expression :
                self._second.to_ssa(ctx)
                second = self._second.get_constraints(ctx)[0]
                second_type = None
            if type(self._second) == Variable :
                second_label = ctx.get_label(self._second.get_name(),Label.prev)
                self._second.set_label(second_label)
                #ctx.set_type(self._first.get_name(),ctx.get_type(f"{self._first}"))
                second = self._second
                if self._second.get_value() is not None :
                    second_type = type(self._second.get_value().get_val())
                else :
                    second_type = ctx.get_type(self._second.get_name())
            elif type(self._second) == Value :
                second = self._second #.get_val()
                second_type = type(self._second.get_val())
            ctx.add(self._first.get_name(),second_type)
            first = ctx.get_label(self._first.get_name(),Label.prev)
            self._constraints += self._make_constraint(ctx,first,second)
        elif self._kind == ExprKind.unary :
            if type(self._first) == Expression :
                self._first.to_ssa(ctx)
                first = self._first.get_constraints(ctx)[0]
            else :
                pass
            self._constraints.append(self._get_z3_operator(first,None,self._operator))

class Call(Exe) :

    def __init__(self, callee: str, params: list, func: Fun = None) -> None :
        self._name = callee
        self._params = params
        self._func = func

    def __str__(self) -> str :
        return f"<Call {self._name}>"

    def __repr__(self) -> str :
        return f"<Call {self._name} at {hex(id(self))}>"

    def get_name(self) -> str :
        return self._name

    def set_fun(self, func: Fun) -> None :
        self._params = func.get_params()
        self._func = func

    def get_constraints(self, ctx: Context = None) -> list :
        ...

    def to_ssa(self, ctx: Context, parent_label: str = None) :
        function_context = self._func.get_local_context()
        for p in self._params :
            p.to_ssa(function_context)
        pass

class Conditional(Exe) :

    def __init__(self, test: Exe, if_block: list, else_block: list = None) -> None :
        self.test = test
        self.if_block = Block(if_block, BlockType.if_block)
        self.else_block = Block(else_block, BlockType.else_block)
        self._constraints = []

    def __str__(self) -> str :
        return f"<Conditional (if/else)>"

    def __repr__(self) -> str :
        return f"<Conditional (if/else) at {hex(id(self))}>"

    def get_test_constraint(self) -> ExprRef :
        return self.test.get_constraints()[0]
    
    def get_test(self) -> Expression :
        return self.test
    
    def _update_ctx(self, ctx: Context) -> None :
        # Merging the two contexts
        new_ctx = Context.merge_context(self.if_block.get_context(),self.else_block.get_context())
        ctx.set_occurrencies(new_ctx.get_occurrencies())
        ctx.set_functions(new_ctx.get_functions())
        ctx.set_types(new_ctx.get_types())

    def _global_diff(self, ctx: Context, modified: list) -> list :
        constraints = []
        for e in modified :
            name = re.sub(remove_ctx_index,"",e)
            index = re.sub(remove_var_name,"",e)
            last_label = ctx.get_label(name,Label.prev)
            last_index = re.sub(remove_var_name,"",last_label)
            t = ctx.get_type(e)
            ctx.add(name,t)
            if index != last_index :
                constraints.append(get_z3_type(e,t) == get_z3_type(last_label,t))
        return constraints
    
    def _diff_from(self, target: dict, source: dict, init_occ: dict) -> list :
        vars = []
        for k in target :
            if k in source and target[k] > source[k] :
                for i in range(source[k]+1,target[k]+1) :
                    vars.append(f"{k}_{i}")
            elif k not in source :
                if k in init_occ:
                    for i in range(init_occ[k]+1,target[k]+1) :
                        vars.append(f"{k}_{i}")
                else :
                    for i in range(target[k]+1) :
                        vars.append(f"{k}_{i}")
        return vars
    
    def _split_var(self, var: str) -> tuple :
        return (re.sub(remove_ctx_index,"",var), int(re.sub(remove_var_name,"",var)))

    def _merge_diff(self, diff_if_else: list, diff_else_if: list) -> list :
        tmp = list(map(self._split_var,diff_if_else + diff_else_if))
        merged = []
        for el in set(map(lambda x: x[0],tmp)) :
            max = 0
            for t in tmp :
                if t[0] == el and t[1] > max :
                    max = t[1]
            merged.append(f"{el}_{max}")
        return merged

    def get_constraints(self, ctx: Context = None) -> list :
        test_constraints = self.test.get_constraints()[0]
        if_block_constraints = And(*self.if_block.get_constraints())
        else_block_constraints = And(*self.else_block.get_constraints())
        return [If(test_constraints,if_block_constraints,else_block_constraints)]
    
    def to_ssa(self, ctx: Context, parent_label: str = None) :
        init_occ = ctx.get_content()[0].copy()
        self.test.to_ssa(ctx)
        self.if_block.to_ssa(ctx)
        self.else_block.to_ssa(ctx)
        
        if_block_updated = {k:v for k,v in self.if_block.get_modified().items()\
                            if k not in init_occ or v != init_occ[k]}

        else_block_updated = {k:v for k,v in self.else_block.get_modified().items()\
                             if k not in init_occ or v != init_occ[k]}
        
        diff_if_else = self._diff_from(if_block_updated,else_block_updated,init_occ)
        diff_else_if = self._diff_from(else_block_updated,if_block_updated,init_occ)
        self.if_block.add_constraints(self._global_diff(self.if_block.get_context(),diff_else_if))
        self.else_block.add_constraints(self._global_diff(self.else_block.get_context(),diff_if_else))
        
        self._update_ctx(ctx)

class Iteration(Exe):

    def __init__(self,kind,test,body) :
        self.kind = kind
        self.test = test
        self.body = body
        self._constraints = []
    
    def __str__(self) -> str :
        return f"<Loop {self.kind}>"

    def __repr__(self) -> str :
        return f"<Loop {self.kind} at {hex(id(self))}>"

    def get_constraints(self, ctx: Context = None) -> list : ...
    
    def to_ssa(self, ctx: Context, parent_label: str = None) :
        pass

class Fun(Exe) :

    def __init__(self, name: str, params: list, body: list, isasync: bool = False) -> None :
        self._name = name
        self._params = params
        self._body = body
        self._async = isasync
        self._local_context = Context()
        self._constraints = []

    def __str__(self) -> str :
        return f"<FUN: {self._name}>"

    def __repr__(self) -> str :
        return f"<FUN: {self._name} at {hex(id(self))}>"
    
    def get_name(self) -> str :
        return self._name

    def get_body(self) -> list :
        return self._body

    def get_params(self) -> list :
        return self._params

    def get_local_context(self) -> Context :
        return self._local_context

    def get_constraints(self, ctx: Context = None) -> list :
        c = []
        for e in self._body :
            c += e.get_constraints()
        return c
    
    def to_ssa(self, ctx: Context, parent_label: str = None) -> None :
        """
        """
        ctx.add_function(self)
        self._local_context.set_parent(ctx)
        for e in self._body :
            e.to_ssa(self._local_context)
            
class Thread(Exe) :
    
    def __init__(self, ctx: Context, content: Block, tid: int) -> None :
        self._ctx = ctx
        self._content = content 
        self._tid = tid
        self._constraints = []
    
    def __repr__(self) -> str :
        return f"<THREAD {self._tid} at {hex(id(self))}>"
    
    def __str__(self) -> str :
        return f"<THREAD {self._tid}>"
    
    def get_constraints(self, ctx: Context = None) -> list :
        pass

    def to_ssa(self, ctx: Context, parent_label: str = None) :
        pass

class Variable(Exe) :

    def __init__(self, name: str, kind: Any = None, value: Value = None) -> None :
        if type(name) != str :
            raise VarTypeException(name)

        self._name = name
        self._kind = kind
        self._value = value
        self._label = None

    def __str__(self) -> str :
        return f"{self._name}"

    def __repr__(self) -> str :
        return f"<Var {self._name} at {hex(id(self))}>"

    def get_label(self) -> str :
        return self._label

    def set_label(self, label: str) -> None:
        self._label = label

    def get_name(self) -> str :
        return self._name

    def get_value(self) -> Value :
        return self._value

    def get_constraints(self, ctx: Context = None) -> list :
        return self._value.get_constraints()

    def to_ssa(self, ctx: Context, parent_label: str = None) :
        # if self._value == Types.undefined :
        #     pass
        if self._value is not None :
            self._value.to_ssa(ctx)