from enum import Enum
from lmb.options import Language
from lmb.flow import Flow
from .javascript.parse import Parser
from .javascript.js_settings import JSSpecifics
import jsbeautifier

class Compiler :

    def __init__(self, source: str, lang: Language) -> None :
        if lang == Language.Javascript :
            # self._flow = Flow(js_specifics)
            self._source = source
            self._parser = Parser(source)
            self._body = self._parser.result()
    
    def get_compiled_source(self) :
        return self._body

    def beautify_source(self) -> str :
        opts = jsbeautifier.default_options()
        opts.max_preserve_newlines = 1
        opts.end_with_newline = True
        return jsbeautifier.beautify(self._source,opts)