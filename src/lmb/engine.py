from .parser.compiler import Compiler, Language
from lmb.structures import Exe, Fun, Call
from lmb.exceptions import InvalidEntryPointException

class Lambda :

    def __init__(self, src: str, lang: Language) -> None :
        comp = Compiler(src, lang)
        self._body = comp.get_compiled_source()
        self._entry_point = None
        self._eq = self._get_equation()

    def _get_equation(self) -> list :
        if self._entry_point is None :
            pass
        return []

    def set_entry_point(self, block_name: str = None) -> None :
        if block_name is None :
            return None

        blocks = [e for e in self._body.get_list() if self._is_main(e)]
        for e in blocks :
            if e.get_name() == block_name :
                self._entry_point = e
            
        if self._entry_point is None :
            raise InvalidEntryPointException()

    def _is_main(self, element: Exe) -> bool :
        return type(element) == Fun