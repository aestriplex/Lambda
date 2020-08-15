from abc import ABC, abstractmethod
from .exceptions import VarTypeException
from .context import Context

class Exe(ABC) :

    _constraints = None

    @abstractmethod
    def to_ssa(self, ctx: Context) :
        pass

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

    def __init__(self) : ...
    
    def to_ssa(self, ctx: Context) : ...

class Object(Exe) :

    def __init__(self) : ...

    def to_ssa(self, ctx: Context) : ...

class String(Exe) :

    def __init__(self) : ...

    def to_ssa(self, ctx: Context) : ...

class BaseType(Exe) :

    def __init__(self) : ...

    def to_ssa(self, ctx: Context) : ...

class Expression(Exe) :

    def __init__(self,kind,operator,first,second = None) :
        self.kind = kind
        self.operator = operator
        self.first = first
        self.second = second

    def __str__(self) :
        return f"<Expr: {self.operator}>"

    def __repr__(self) :
        return f"<Expr: {self.operator} at {hex(id(self))}>"

    def to_ssa(self, ctx: Context) :
        pass

class Call(Exe) :

    def __init__(self,callee,params) :
        self._callee = callee
        self._params = params

    def __str__(self) :
        return f"<CALL {self._callee}>"

    def __repr__(self) :
        return f"<CALL {self._callee} at {hex(id(self))}>"

    def to_ssa(self, ctx: Context) :
        pass

class Conditional(Exe) :

    def __init__(self,test,if_block,else_block) :
        self.test = test
        self.if_block = if_block
        self.else_block = else_block

    def __str__(self) :
        return f"<Conditional>"

    def __repr__(self) :
        if self.else_block is None :
            return f"<Conditional (IF) at {hex(id(self))}>"
        return f"<Conditional (IF/ELSE) at {hex(id(self))}>"
    
    def to_ssa(self, ctx: Context) :
        pass

class Iteration(Exe) :

    def __init__(self,kind,test,body) :
        self.kind = kind
        self.test = test
        self.body = body
    
    def __str__(self) :
        return f"<Loop: {self.kind}>"

    def __repr__(self) :
        return f"<Loop: {self.kind} at {hex(id(self))}>"
    
    def to_ssa(self, ctx: Context) :
        pass

class Fun(Exe) :

    def __init__(self,name,params,body,isasync) :
        self._name = name
        self._params = params
        self._body = body
        self._async = isasync

    def __str__(self) :
        return f"<FUN: {self._name}>"

    def __repr__(self) :
        return f"<FUN: {self._name} at {hex(id(self))}>"
    
    def to_ssa(self, ctx: Context) :
        pass

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
    
    def to_ssa(self, ctx: Context) :
        if self._value is not None :
            self._value.to_ssa(ctx)