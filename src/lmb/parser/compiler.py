from enum import Enum
from .javascript.parse import Parser

class Language(Enum) :
    Javascript = 0x00

class Compiler :

    def __init__(self, source: str, lang: Language) -> None :
        if lang == Language.Javascript :
            self._parser = Parser(source)
            self._body = self._parser.result()
    
    def get_compiled_source(self) :
        return self._body