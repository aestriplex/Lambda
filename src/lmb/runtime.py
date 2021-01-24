from lmb.structures import Body, Expression
from enum import Enum
from z3 import ExprRef, ModelRef, CheckSatResult, sat, unsat

class Mode(Enum) :
    detect_unreachable   = 0x00
    post_conditions = 0x01

class Runtime :

    def __init__(self, body: Body = None) -> None :
        self._body = body
        self._conditions = None
    
    def add_condition(self, condition: Expression, result: CheckSatResult, model: ModelRef = None) -> None :
        if model is None :
            pass
        else :
            pass