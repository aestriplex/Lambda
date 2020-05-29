from z3 import *

LPAR = '('
RPAR = ')'

def init_stack(st) :
    return st.index == 0

def search_err(st) :
    return If(st.index == 0, True, False)

def push_par(st,par):
    pass

class Stack :

    def __init__(self,n) :
        self.index = [Int(f"index{i}") for i in range(n)]
        self.cont = String("cont")

string = input("> ")

stack = Stack(len(string))
s = Solver()
s.add(init_stack(stack))

for c in string :
    if c == LPAR or c == RPAR :
        push_par(stack, c)
