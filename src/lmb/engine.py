from typing import Any
from z3 import And, Not, Solver, sat, unsat, Datatype, Const
from enum import Enum
from .options import Language
from .parser.compiler import Compiler
from .context import Context
from .structures import Body, Exe, Fun, Call, Expression, Variable, Conditional, set_global_datatypes
from .exceptions import InvalidEntryPointException, InvalidModeException
from .runtime import Runtime, Mode, Outcome

class Scope(Enum) :
    full  = 0x00
    local = 0x01

class Lambda :
    """
    """
    def __init__(
                self, 
                src: str, 
                lang: Language, 
                mode: Mode = None, 
                uninterpreted: list = None) -> None :
        set_global_datatypes()
        comp = Compiler(src, lang)
        self._body = comp.get_compiled_source()
        self._solver = Solver()
        self._uninterpreted = uninterpreted
        self._entry_point = self._body
        self._scope = Scope.full
        self._conditionals = None
        if mode is None :
            self._mode = Mode.detect_unreachable
        else :
            self._mode = mode

    def get_equation(self) -> And :
        """
        It returns the Z3 object corresponding to the SSA translation of the program
        """
        return And(*self.get_constraints())

    def _get_conditionals(self) -> list :
        return []

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

    def _build_calls(self, body: list) -> None :
        ctx = self._entry_point.get_context()
        functions = ctx.get_functions()
        for e in body :
            if hasattr(e,"get_body") :
                self._build_calls(e.get_body())
            elif type(e) == Call :
                name = e.get_name()
                e.set_fun(functions[name])
                e.to_ssa()

    def build(self) -> None :
        if self._scope == Scope.local :
            calls = self._get_calls(self._entry_point.get_list())
            expr = self._get_expressions(self._entry_point.get_list())
            self._entry_point += self._get_global_variables(expr)
            self._entry_point += calls
        self._entry_point.build_body()
        self._build_calls(self._entry_point.get_list())

    def set_entry_point(self, block_name: str = None) -> None :
        """
        By default the entry point is the whole source.

        You can set a local entry point by passing it the name of a function
        """
        if block_name is not None :
            blocks = [e for e in self._body.get_list() if self._is_main(e)]
            for e in blocks :
                if e.get_name() == block_name :
                    self._entry_point = Body([e])
                    self._scope = Scope.local
                
            if self._scope == Scope.full :
                raise InvalidEntryPointException()

    def _add_to_solver(self, element: Exe, body: list, runtime: Runtime) -> None :
        if type(element) == Conditional :
            self._solver.add(And(*body))
            self._solver.push()
            post = element.get_test_constraint()
            self._solver.add(post)
            res = self._solver.check()
            if res == unsat :
                runtime.add_to_result(element.get_test(), Outcome.unreachable)
            else :
                self._solver.pop()
                self._solver.push()
                self._solver.add(Not(post))
                if self._solver.check() == unsat :
                    runtime.add_to_result(element.get_test(), Outcome.useless)
                else :
                    runtime.add_to_result(element.get_test(), Outcome.ok)
            self._solver.pop()
            body += element.get_constraints()
        elif type(element) != Fun :
            body += element.get_constraints()

    def _detect_unreachable(self) -> Runtime :
        runtime = Runtime()
        body = []
        for e in self._entry_point.get_list() :
            if type(e) == Fun :
                for b in e.get_body() :
                    self._add_to_solver(b, body, runtime)
            else :
                self._add_to_solver(e, body, runtime)
        return runtime

    def check(self) -> Runtime :
        if self._mode == Mode.detect_unreachable :
            runtime = self._detect_unreachable()
        elif self._mode == Mode.post_conditions :
            runtime = Runtime()

        return runtime.get_result()

    def set_post_condition(self, condition: Any, line: int) :
        if self._mode == Mode.detect_unreachable :
            raise InvalidModeException()