from z3 import Solver, String, StringVal, Length, And, Not, sat

def init(strings, input_strings) :
    for s,i_s in zip(strings,input_strings) :
        yield s == StringVal(i_s)

def tran(strings,l) :
    for s in strings :
        yield Length(s) <= l


n = int(input("number of strings: "))

input_strings = [input(f"string {i}: ") for i in range(1,n+1)]
strings = [String(f"s_{i}") for i in range(n)]

l = int(input("max length: "))

s = Solver()

init_condition = init(strings,input_strings)
s.add(And(*init_condition))

tran_condition = tran(strings,l)
s.add(Not(And(*tran_condition)))

if s.check() == sat :
    print(f"counterexample:\n{s.model()}")
else :
    print("valid")