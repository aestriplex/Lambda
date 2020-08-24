from typing import Any
from z3 import And
from .parser.compiler import Compiler, Language
from lmb.context import Context
from lmb.structures import Body, Exe, Fun, Call, Expression, Variable
from lmb.exceptions import InvalidEntryPointException

class Lambda :

    def __init__(self, src: str, lang: Language) -> None :
        comp = Compiler(src, lang)
        self._body = comp.get_compiled_source()
        self._entry_point = None
        #self._eq = self._get_equation()

    def _get_equation(self) -> And :
        return And(*self.get_constraints())

    def _get_conditionals(self) -> list :
        return []

    def detect_unreachable(self) -> None : ...

    def get_constraints(self) -> list :
        c = []
        for e in self._body.get_list() :
            c += e.get_constraints()
        return c

    def _is_main(self, element: Exe) -> bool :
        return type(element) == Fun

    def _get_calls(self, body: list) -> list :
        return [e for e in body if type(e) == Call]

    def _get_expressions(self, body: list) -> list :
        return [e for e in body if type(e) == Expression]

    def _get_declared_vars(self, body: list) -> list :
        return [e.get_name() for e in body if type(e) == Variable]

    def _get_global_variables(self, expr: list) -> list :
        declared_vars = self._get_declared_vars(self._entry_point.get_list())
        filter_func = lambda x: x.get_first() in declared_vars or \
                                x.get_second() in declared_vars
        return list(filter(filter_func,expr))

    def build(self) -> None :
        if self._entry_point is None :
            self._body.build_body()
        else :
            calls = self._get_calls(self._entry_point.get_list())
            expr = self._get_expressions(self._entry_point.get_list())
            self._entry_point += self._get_global_variables(expr)
            self._entry_point += calls

    def set_entry_point(self, block_name: str = None) -> None :
        if block_name is not None :
            blocks = [e for e in self._body.get_list() if self._is_main(e)]
            for e in blocks :
                if e.get_name() == block_name :
                    self._entry_point = Body([e])
                
            if self._entry_point is None :
                raise InvalidEntryPointException()

    def set_post_condition(self, condition: Any, line: int) : ...