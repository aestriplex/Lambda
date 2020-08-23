from __future__ import annotations
import re
from abc import ABC, abstractmethod
from .exceptions import VarTypeException
from .context import Context, Label
from typing import Any, Generator
from z3 import Int, Real, String, StringVal

_ANONYMOUS = "Anonymous"

class Exe(ABC) :

    @abstractmethod
    def get_constraints(self, ctx: Context = None) -> list : ...

    @abstractmethod
    def to_ssa(self, ctx: Context, parent_label: str = None) : ...

class Body() :

    def __init__(self, lst: list) -> None :
        self._content = lst
        self._global_context = Context()

    def __str__(self) -> str :
        var = "var" if len(self._content) == 0 else "vars"
        return f"<BODY ({len(self._content)} {var})>"

    def __repr__(self) -> str :
        var = "var" if len(self._content) == 0 else "vars"
        return f"<BODY ({len(self._content)} {var}) at {hex(id(self))}>"

    def _get_body_repr(self, body: list, s: str) -> str:
        pass
    
    def remove_first(self) -> None :
        del self._content[0]

    def remove_last(self) -> None :
        del self._content[-1]

    def get_list(self) -> list :
        return self._content
    
    def build_body(self) -> None :
        for e in self._content :
            e.to_ssa(self._global_context)

class Array(Exe) :

    def __init__(self, name: str, content: list) -> None :
        self._name = _ANONYMOUS if name is None else name
        self._content = content
        self._constraints = []

    def __str__(self) -> str :
        return f"<Array {self._name}>"

    def __repr__(self) -> str :
        return f"<Array {self._name} at {hex(id(self))}>"

    def _clean_label(self, label: str) -> str :
        return re.sub(r"\_[0-9]","",label)

    def _find_label(self, ctx: Context, val: Exe, i: int, parent_label: str) -> str :
        if self._name == _ANONYMOUS :
            lbl = f"[{i}]"
        else :
            lbl = f"{self._name}[{i}]"
        if parent_label is not None :
            lbl = f"{self._clean_label(parent_label)}{lbl}"
        ctx.add(lbl)
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

    def _clean_label(self, label: str) -> str :
        return re.sub(r"\_[0-9]","",label)

    def _find_label(self, ctx: Context, val: Exe, key: str, parent_label: str) -> str :
        if self._name == _ANONYMOUS :
            lbl = f"{key}"
        else :
            lbl = f"{self._name}.{key}"
        if parent_label is not None :
            lbl = f"{self._clean_label(parent_label)}.{lbl}"
        ctx.add(lbl)
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

    def __init__(self, name: str, val: Any)  -> None :
        self._name = _ANONYMOUS if name is None else name
        self._content = val
        self._constraints = []

    def __str__(self) -> str :
        return f"<Value ({type(self._content).__name__})>"

    def __repr__(self) -> str :
        return f"<Value ({type(self._content).__name__}) at {hex(id(self))}>"

    def _find_label(self, ctx: Context) -> str :
        ctx.add(self._name)
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

class Expression(Exe) :

    def __init__(self,kind,operator,first,second = None) :
        self.kind = kind
        self.operator = operator
        self.first = first
        self.second = second
        self._constraints = []

    def __str__(self) -> str :
        return f"<Expr: {self.operator} ({self.kind.name})>"

    def __repr__(self) -> str :
        return f"<Expr: {self.operator} ({self.kind.name}) at {hex(id(self))}>"

    def get_constraints(self, ctx: Context = None) -> list : ...

    def to_ssa(self, ctx: Context, parent_label: str = None) -> None :
        pass

class Call(Exe) :

    def __init__(self, callee: str, params: list, func: Fun) -> None :
        self._name = callee
        self._params = params
        self._func = func

    def __str__(self) -> str :
        return f"<CALL {self._name}>"

    def __repr__(self) -> str :
        return f"<CALL {self._name} at {hex(id(self))}>"

    def get_name(self) -> str :
        return self._name

    def get_constraints(self, ctx: Context = None) -> list :
        ...

    def to_ssa(self, ctx: Context, parent_label: str = None) :
        function_context = self._func.get_local_context()
        for p in self._params :
            p.to_ssa(function_context)

class Conditional(Exe) :

    def __init__(self,test,if_block,else_block) :
        self.test = test
        self.if_block = if_block
        self.else_block = else_block
        self._constraints = []

    def __str__(self) :
        return f"<Conditional>"

    def __repr__(self) :
        if self.else_block is None :
            return f"<Conditional (IF) at {hex(id(self))}>"
        return f"<Conditional (IF/ELSE) at {hex(id(self))}>"

    def get_constraints(self, ctx: Context = None) -> list : ...
    
    def to_ssa(self, ctx: Context, parent_label: str = None) :
        pass

class Iteration(Exe) :

    def __init__(self,kind,test,body) :
        self.kind = kind
        self.test = test
        self.body = body
        self._constraints = []
    
    def __str__(self) -> str :
        return f"<Loop: {self.kind}>"

    def __repr__(self) -> str :
        return f"<Loop: {self.kind} at {hex(id(self))}>"

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
        self._local_context.set_parent(ctx)
        for e in self._body :
            e.to_ssa(self._local_context)

class Variable(Exe) :

    def __init__(self,name,kind,value = None) :
        if type(name) != str :
            raise VarTypeException(name)

        self._name = name
        self._kind = kind
        self._value = value

    def __str__(self) :
        return f"<VAR: {self._name}>"

    def __repr__(self) :
        return f"<VAR: {self._name} at {hex(id(self))}>"

    def get_constraints(self, ctx: Context = None) -> list :
        return self._value.get_constraints()

    def to_ssa(self, ctx: Context, parent_label: str = None) :
        if self._value is not None :
            self._value.to_ssa(ctx)