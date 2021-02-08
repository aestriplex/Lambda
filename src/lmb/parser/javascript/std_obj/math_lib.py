from typing import List, Tuple, Any
from z3 import *

Axiomatized = Tuple[List,Any]

class StdMath :

    # Properties
    e        = 2.718281828459045
    ln2      = 0.6931471805599453
    ln10     = 2.302585092994046
    log2e    = 1.4426950408889634
    log10e   = 0.43429448190325176
    pi       = 3.141592653589793
    sqrt1_2  = 0.7071067811865476
    sqrt2    = 1.4142135623730951

    # Functions
    @staticmethod
    def abs(x: z3) -> Axiomatized :
        return [], If(x < 0, -1 * x, x)
    
    @staticmethod
    def sign(x: z3) -> Axiomatized :
        return [], If(x > 0, 1, If(x==0,0,-1))
    
    @staticmethod
    def exp(x: z3) -> Axiomatized :
        f = Function("exp", RealSort(), RealSort())
        y = Real("y")
        axioms = [
            f(0) == 1,
            f(1) == StdMath.e,
            f(x) > 0,
            f(x+y) == f(x)*f(y)
        ]
        return axioms, f(x)

    @staticmethod
    def max(nums: list) -> Axiomatized :
        pass

    @staticmethod
    def min(nums: list) -> Axiomatized :
        pass
