from abc import ABC, abstractmethod
from typing import Any
from .context import Context, Label
from .exceptions import CommandNotFoundException, CommandParseException, UnknownTypeException

class Cmd :
    _type      = "type"
    _value     = "value"
    constraint = "constraint"

class InitTypes :
    _int       = "int"
    _float     = "float"
    _string    = "string"
    _null      = "null"
    _undefined = "undefined"

class Command(ABC) :

    def __init__(self, command: str, var: str) -> None :
        self._command = command
        self._var = var

    @abstractmethod
    def execute(self, ctx: Context) -> list : ...

class TypeInit(Command) :

    def _parse_type(self, t: str) -> Any :
        if t == InitTypes._int :
            return int
        elif t == InitTypes._float :
            return float
        elif t == InitTypes._string :
            return str
        elif t == InitTypes._null :
            pass
        elif t == InitTypes._undefined :
            pass
        else :
            raise UnknownTypeException(t)

    def execute(self, ctx: Context) -> list :
        ctx.add(self._var,self._parse_type(self._command))
        return []

class ValueInit(Command) :

    def execute(self, ctx: Context) -> list : ...

class ConstraintInit(Command) :

    def execute(self, ctx: Context) -> list : ...

class EntryPoint :

    def __init__(self, name: str, init: dict) -> None :
        self._name = name
        self._init = init
        self._cmds = self._process_init(init)

    def get_name(self) -> str :
        return self._name
    
    def get_params(self) -> tuple :
        return tuple(self._init.keys())

    def execute(self, ctx: Context) -> list :
        a = []
        for cmd in self._cmds :
            a.append(cmd.execute(ctx))
        return a

    def _parse_command(self, value: str, var: str) -> Command :
        _t,_v = value.split(":")
        if not (_t or _v) :
            raise CommandParseException(value)

        if _t == Cmd._type :
            return TypeInit(_v,var)
        elif _t == Cmd._value :
            return ValueInit(_v,var)
        elif _t == Cmd.constraint :
            return ConstraintInit(_v,var)
        else :
            raise CommandNotFoundException(_t)
        
    def _process_init(self, init: dict) -> list :
        """
        input dict has the following structure:
            {
                <var name> : <<command>:<value>>
            }
        
        This function has to parse the input dict in order to build a list of
        commands.
        """
        return [self._parse_command(value,key) for key, value in init.items()]
             