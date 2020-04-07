from abc import ABC, abstractmethod
from exceptions import VarTypeException

class Exe(ABC) :

    @abstractmethod
    def to_ssa(self) :
        pass

class Expression(Exe) :

    def __init__(self,kind,operator,first,second = None) :
        self.kind = kind
        self.operator = operator
        self.first = first
        self.second = second

    def __str__(self) :
        return f"<Expr: {self.operator}>"
    
    def to_ssa(self) :
        pass

class Call(Exe) :

    def __init__(self,callee,params) :
        self._callee = callee
        self._params = params

    def __str__(self) :
        return f"<CALL {self._callee}>"

    def to_ssa(self) :
        pass

class Conditional(Exe) :

    def __init__(self,test,if_block,else_block) :
        self.test = test
        self.first = if_block
        self.second = else_block

    def __str__(self) :
        return f"<Conditional>"
    
    def to_ssa(self) :
        pass

class Iteration(Exe) :

    def __init__(self,kind,test,body) :
        self.kind = kind
        self.test = test
        self.body = body
    
    def __str__(self) :
        return f"<Loop: {self.kind}>"
    
    def to_ssa(self) :
        pass

class Fun(Exe) :

    def __init__(self,name,params,body,isasync) :
        self._name = name
        self._params = params
        self._body = body
        self._async = isasync

    def __str__(self) :
        return f"<FUN: {self._name}>"
    
    def to_ssa(self) :
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
    
    def to_ssa(self) :
        pass

class Context :
    
    def __init__(self) :
        self._occurrencies = {}
        self._assertions = []

    def __src__(self) :
        return f""

    def add(self,occurrence) :
        pass