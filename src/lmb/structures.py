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
    def _find_labels(self, ctx: Context) -> list :
        pass

    @abstractmethod
    def to_ssa(self, ctx: Context, parent_label: str = None) :
        pass

class Body() :

    def __init__(self, lst: list) -> None :
        self._content = lst

    def __str__(self) -> str :
        var = "var" if len(self._content) == 0 else "vars"
        return f"<BODY ({len(self._content)} {var})>"

    def __repr__(self) -> str :
        var = "var" if len(self._content) == 0 else "vars"
        return f"<BODY ({len(self._content)} {var}) at {hex(id(self))}>"

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
        self._name = _ANONYMOUS if name is None else name
        self._content = content
        self._constraints = []

    def __str__(self) -> str :
        return f"<Array {self._name}>"

    def __repr__(self) -> str :
        return f"<Array {self._name} at {hex(id(self))}>"

    def _clean_label(self, label: str) -> str :
        return re.sub(r"\_[0-9]","",label)

    def _find_labels(self, ctx: Context) -> Generator :
        i = 0
        for _ in self._content :
            if self._name == _ANONYMOUS :
                lbl = f"[{i}]"
            else :
                lbl = f"{self._name}[{i}]"
            i += 1
            ctx.add(lbl)
            yield ctx.get_label(lbl,Label.prev)
    
    def to_ssa(self, ctx: Context, parent_label: str = None) -> None :
        labels = self._find_labels(ctx)
        for lbl,val in zip(labels,self._content) :
            if parent_label is not None :
                lbl = f"{parent_label}{lbl}"
            if type(val) != Value :
                lbl = self._clean_label(lbl)
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

    def _find_labels(self, ctx: Context) -> Generator :
        for key in self._content :
            if self._name == _ANONYMOUS :
                lbl = f".{key}"
            else :
                lbl = f"{self._name}.{key}"
            ctx.add(lbl)
            yield ctx.get_label(lbl,Label.prev)

    def to_ssa(self, ctx: Context, parent_label: str = None) -> None :
        labels = self._find_labels(ctx)
        for lbl,val in zip(labels,self._content.values()) :
            if parent_label is not None :
                lbl = f"{parent_label}.{lbl}"
            if type(val) != Value :
                lbl = self._clean_label(lbl)
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

    def _find_labels(self, ctx: Context) -> Generator :
        ctx.add(self._name)
        yield ctx.get_label(self._name,Label.prev)

    def to_ssa(self, ctx: Context, parent_label: str = None) -> None :
        if parent_label is not None :
            if type(self._content) == int :
                self._constraints.append(Int(parent_label) == self._content)
            elif type(self._content) == float :
                self._constraints.append(Real(parent_label) == self._content)
            elif type(self._content) == str :
                self._constraints.append(String(parent_label) == StringVal(self._content))

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

    def _find_labels(self, ctx: Context) -> Generator :
        pass

    def to_ssa(self, ctx: Context, parent_label: str = None) -> None :
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

    def to_ssa(self, ctx: Context, parent_label: str = None) :
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

    def _find_labels(self, ctx: Context) -> Generator :
        pass
    
    def to_ssa(self, ctx: Context, parent_label: str = None) :
        pass

class Fun(Exe) :

    def __init__(self,name: str, params: list, body: list, isasync: bool = False) -> None :
        self._name = name
        self._params = params
        self._body = body
        self._async = isasync
        self._local_context = Context()

    def __str__(self) -> str :
        return f"<FUN: {self._name}>"

    def __repr__(self) -> str :
        return f"<FUN: {self._name} at {hex(id(self))}>"
    
    def get_name(self) -> str :
        return self._name

    def _find_labels(self, ctx: Context) -> Generator :
        pass
    
    def to_ssa(self, ctx: Context, parent_label: str = None) :
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

    def to_ssa(self, ctx: Context, parent_label: str = None) :
        if self._value is not None :
            self._value.to_ssa(ctx)