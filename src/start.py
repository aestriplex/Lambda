from lmb.parser.compiler import Language
from lmb.engine import Lambda, EntryPoint
from pathlib import Path

with open(Path(__file__).parent / "test.js","r") as f :
    src = f.read()

l = Lambda(src, Language.Javascript)
init = {"tmp": "type:int"}
ep = EntryPoint("f2",init)
l.set_entry_point(ep)
l.build()
print(l.get_equation())
for a in l.check() :
    print(a)
