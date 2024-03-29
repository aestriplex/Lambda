from typing import List, Tuple
from lmb.structures import Body, Expression
from lmb.utils import remove_ctx_index
import re
from enum import Enum
from z3 import ExprRef, ModelRef

Model = List[str]
Row = Tuple[str, str, int, Model]
Result = List[Row]

class Mode(Enum) :
    detect_unreachable  = 0x00
    post_conditions     = 0x01

class Outcome(Enum) :
    ok           = 0x00
    unreachable  = 0x01
    useless      = 0x02

class Runtime :

    def __init__(self, source: str = None, body: Body = None) -> None :
        self._body = body
        self._src = source
        self._result = []

    def get_split_source(self) -> list :
        return self._src.split("\n")

    def get_source(self) -> str :
        return self._src

    def _get_var_label(self, instance: str) -> str :
        return re.sub(remove_ctx_index, "", instance)

    def _model_to_str(self, model: ModelRef) -> str :
        if model is None :
            return "-"
        return "\n".join([f"{self._get_var_label(m.name())} {model[m]}" for m in model])
    
    def add_to_result(self, condition: Expression, outcome: Outcome, model: ModelRef = None) -> None :
        self._result.append([str(condition), outcome.name, outcome.value, condition.get_lineno(), self._model_to_str(model)])
    
    def get_result(self) -> Result :
        """
        """
        return self._result