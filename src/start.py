from lmb.parser.compiler import Compiler, Language
from lmb.engine import Lambda

with open(r".\src\test.js","r") as f :
    # comp = Compiler(f.read(), Language.Javascript)
    # b = comp.get_compiled_source()
    l = Lambda(f.read(), Language.Javascript)
    l.set_entry_point()
    l.build()
    end = "end"