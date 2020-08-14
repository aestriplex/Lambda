from lmb.parser.compiler import Compiler, Language

with open(r"C:\Users\mnicoli\Documents\GitHub\Lambda\src\test.js","r") as f :
    comp = Compiler(f.read(), Language.Javascript)
    b = comp.get_compiled_source()
    end = "end"