from __future__ import annotations
from abc import ABC, abstractmethod
from .exceptions import VarTypeException
from .context import Context, Label
from typing import Any, Generator
from z3 import Int, Real

class Exe(ABC) :

    @abstractmethod
    def _find_labels(self, ctx: Context) -> list :
        pass

    @abstractmethod
    def to_ssa(self, ctx: Context) :
        pass

class Body() :

    def __init__(self, lst: list) -> None :
        self._content = lst

    def __str__(self) -> str :
        pass

    def __repr__(self) -> str :
        return f"<BODY ({len(self._content)}) at {hex(id(self))}>"

    def _build_body_repr(self, body: list, s: str) -> str:
        pass
    
    def remove_first(self) -> None :
        del self._content[0]

    def remove_last(self) -> None :
        del self._content[-1]

    def get_list(self) -> list :
        return self._content

class Array(Exe) :

    def __init__(self, name: str, content: list) -> None :
        self._name = name
        self._content = content
        self._constraints = []

    def _find_labels(self, ctx: Context) -> Generator :
        i = 0
        for _ in self._content :
            lbl = f"{self._name}[{i}]"
            i += 1
            ctx.add(lbl)
            yield ctx.get_label(lbl,Label.prev)
    
    def to_ssa(self, ctx: Context) :
        labels = self._find_labels(ctx)
        for lbl,val in zip(labels,self._content) :
            if type(val) == int :
                self._constraints.append(Int(lbl) == val)
            elif type(val) == float :
                self._constraints.append(Real(lbl) == val)

class Object(Exe) :

    def __init__(self, name: str, content: dict) -> None :
        self._name = name
        self._content = content
        self._constraints = []

    def _find_labels(self, ctx: Context) -> Generator :
        for key in self._content :
            lbl = f"{self._name}.{key}"
            ctx.add(lbl)
            yield ctx.get_label(lbl,Label.prev)

    def to_ssa(self, ctx: Context) -> None :
        labels = self._find_labels(ctx)
        for lbl,val in zip(labels,self._content.values()) :
            if type(val) == int :
                self._constraints.append(Int(lbl) == val)
            elif type(val) == float :
                self._constraints.append(Real(lbl) == val)

# class String(Exe) :

#     def __init__(self, name: str, content: dict) -> None :
#         self._name = name
#         self._content = content

#     def to_ssa(self, ctx: Context) :
#         ctx.add(self._name)
#         self._constraints.append(ctx.get_label(self._name,Label.curr))

class Value(Exe) :

    def __init__(self) : ...

    def _find_labels(self, ctx: Context) -> Generator :
        pass

    def to_ssa(self, ctx: Context) : ...

class Expression(Exe) :

    def __init__(self,kind,operator,first,second = None) :
        self.kind = kind
        self.operator = operator
        self.first = first
        self.second = second
        self._constraints = []

    def __str__(self) :
        return f"<Expr: {self.operator}>"

    def __repr__(self) :
        return f"<Expr: {self.operator} at {hex(id(self))}>"

    def _find_labels(self, ctx: Context) -> Generator :
        pass

    def to_ssa(self, ctx: Context) :
        pass

class Call(Exe) :

    def __init__(self,callee,params) -> None :
        self._name = callee
        self._params = params

    def __str__(self) -> str :
        return f"<CALL {self._name}>"

    def __repr__(self) -> str :
        return f"<CALL {self._name} at {hex(id(self))}>"

    def get_name(self) -> str :
        return self._name

    def _find_labels(self, ctx: Context) -> Generator :
        pass

    def to_ssa(self, ctx: Context) :
        pass

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

    def _find_labels(self, ctx: Context) -> Generator :
        pass
    
    def to_ssa(self, ctx: Context) :
        pass

class Iteration(Exe) :

    def __init__(self,kind,test,body) :
        self.kind = kind
        self.test = test
        self.body = body
        self._constraints = []
    
    def __str__(self) :
        return f"<Loop: {self.kind}>"

    def __repr__(self) :
        return f"<Loop: {self.kind} at {hex(id(self))}>"

    def _find_labels(self, ctx: Context) -> Generator :
        pass
    
    def to_ssa(self, ctx: Context) :
        pass

class Fun(Exe) :

    def __init__(self,name,params,body,isasync) -> None :
        self._name = name
        self._params = params
        self._body = body
        self._async = isasync

    def __str__(self) -> str :
        return f"<FUN: {self._name}>"

    def __repr__(self) -> str :
        return f"<FUN: {self._name} at {hex(id(self))}>"
    
    def get_name(self) -> str :
        return self._name

    def _find_labels(self, ctx: Context) -> Generator :
        pass
    
    def to_ssa(self, ctx: Context) :
        for e in self._body :
            e.to_ssa(ctx)

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

    def _find_labels(self, ctx: Context) -> Generator :
        pass

    def to_ssa(self, ctx: Context) :
        if self._value is not None :
            self._value.to_ssa(ctx)