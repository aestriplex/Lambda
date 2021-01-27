""" 
    File name:    Sample4.py

    Copyright (c) May, 2020 - Matteo Nicoli

    /* Code wants to break free */
"""

from z3 import Solver, Int, And, Not, sat

def init(values,input_values) :
    for v,i_s in zip(values,input_values) :
        yield v == i_s

def tran(values) :
    if values == [] or values[1:] == [] :
        return True
    if values[1:] is not None :
        return And(values[0] <= values[1],tran(values[1:]))

n = int(input("number of integers: "))

input_values = [int(input(f"number {i}: ")) for i in range(1,n+1)]
values = [Int(f"s_{i}") for i in range(n)]

s = Solver()

init_condition = init(values,input_values)
s.add(And(*init_condition))

tran_condition = tran(values)
s.add(Not(tran_condition))

if s.check() == sat :
    print(f"counterexample:\n{s.model()}")
else :
    print("valid")