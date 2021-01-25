from lmb.parser.compiler import Compiler, Language
from lmb.engine import Lambda
from pathlib import Path

with open(Path(__file__).parent / "test.js","r") as f :
    src = f.read()

l = Lambda(src, Language.Javascript)
l.set_entry_point()
l.build()
print(l.get_equation())
for a in l.check() :
    print(a)
end = "end"