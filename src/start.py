from lmb.parser.compiler import Compiler, Language
from lmb.engine import Lambda


with open(r"C:\Users\mnicoli\Documents\GitHub\Lambda\src\test.js","r") as f :
    # comp = Compiler(f.read(), Language.Javascript)
    # b = comp.get_compiled_source()
    l = Lambda(f.read(), Language.Javascript)
    l.build()
    end = "end"