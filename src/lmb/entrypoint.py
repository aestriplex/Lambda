from __future__ import annotations
from abc import ABC, abstractmethod
from z3 import Int, Real, String, StringVal
from typing import Any
from .context import Context, Label, z3ctx
from .structures import Pointer
from .exceptions import CommandNotFoundException, CommandParseException, UnknownTypeException, InconsistentTypeException, UnimplementedFeatureException, InitValueException

class Cmd :
    _type      = "type"
    _value     = "value"
    constraint = "constraint"

class InitTypes :
    _int       = "int"
    _float     = "float"
    _string    = "string"
    _null      = "null"

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
            return Pointer("0x00", self._var)
        else :
            raise UnknownTypeException(t)

    def execute(self, ctx: Context) -> list :
        _type = self._parse_type(self._command)

        if type(_type) == Pointer :
            # the variable is initialized to null
            _type.to_ssa(ctx)
            return _type.get_constraints(ctx)[0]
        
        ctx.add(self._var,_type)

class ValueInit(Command) :

    # def _is_digit(self, value: str) -> int | float | None :
    #     n_dots = 0
    #     for c in value :
    #         if not c.isdigit() :
    #             if c == '.' :
    #                 n_dots += 1
    #             else :
    #                 return None
    #     if c == 0  :
    #         return Int(self._var) == int(value)
    #     if c == 1 :
    #         return Real(self._var) == float(value)
    #     return None

    # def _parse_str(self, value: str) -> Any :
    #     if value == InitTypes._null :
    #         raise UnimplementedFeatureException(value)
    #     if value == InitTypes._undefined :
    #         raise UnimplementedFeatureException(value)
    #     return String(self._var) == StringVal(value)
    
    # def _parse_type(self, value: str) -> Any :
    #     val = self._is_digit(value)
    #     return val if val else self._parse_str(value)

    def _parse_type(self, t: str) -> Any :
        assert t != InitTypes._null, "Cannot be assigned a value of type `null`"

        if t == InitTypes._int :
            return int
        elif t == InitTypes._float :
            return float
        elif t == InitTypes._string :
            return str
        else :
            raise UnknownTypeException(t)

    def _get_expr(self, _type: Any, value: str, label: str) -> Any :
        if _type == int :
            return Int(label, z3ctx) == int(value)
        if _type == float :
            return Real(label, z3ctx) == float(value)
        if _type == str :
            return String(label, z3ctx) == StringVal(value, z3ctx)

    def execute(self, ctx: Context) -> list :
        
        index = self._command.find(":")
        if index == -1 :
            raise InitValueException(self._command)

        _t, _v = self._parse_type(self._command[:index]), self._command[index+1:]
        ctx.add(self._var, _t)
        lbl = ctx.get_label(self._var,Label.prev)
        return self._get_expr(_t,_v,lbl)


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
            constraint = cmd.execute(ctx)
            if constraint is not None :
                a.append(constraint)
        return a

    def _parse_command(self, value: str, var: str) -> Command :
        index = value.find(":")
        if index == -1 :
            raise CommandParseException(value)

        _t, _v = value[:index], value[index+1:]

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
             