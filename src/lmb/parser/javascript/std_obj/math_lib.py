from typing import List, Tuple, Any
import random
from z3 import z3, If, Function, Real, RealSort, And, ToInt, StringVal, Or

rand_occ = 0

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
    def expm1(x: z3) -> Axiomatized :
        axioms, f = StdMath.exp(x)
        return axioms, f(x) - 1
    
    @staticmethod
    def _common_trig_fun(f: Function, g: Function, x: Real) -> list :
        return [And(f(x) >= -1,f(x) <= 1), f(x)**2 + g(x)**2 == 1]

    @staticmethod
    def sin(x: z3) -> Axiomatized :
        f = Function("sin", RealSort(), RealSort())
        g = Function("cos", RealSort(), RealSort())
        axioms = StdMath._common_trig_fun(f,g,x) + [
            f(-1*x) == -1* f(x),
            f(0) == 0,
            f(StdMath.pi/2) == 1
        ]
        return axioms, f(x)
    
    @staticmethod
    def cos(x: z3) -> Axiomatized :
        f = Function("cos", RealSort(), RealSort())
        g = Function("sin", RealSort(), RealSort())
        axioms = StdMath._common_trig_fun(f,g,x) + [
            f(-1*x) == f(-1*x),
            f(0) == 1,
            f(StdMath.pi/2) == 0
        ]
        return axioms, f(x)

    @staticmethod
    def trunc(x: z3) -> Axiomatized :
        return [], ToInt(x)

    @staticmethod
    def to_source() -> Axiomatized :
        return [], StringVal("Math")

    @staticmethod
    def random() -> Axiomatized :
        global rand_occ
        n = Real(f"__rand_r_{rand_occ}")
        rand_occ += 1
        return [n == random.random()], n

    @staticmethod
    def floor(x: z3) -> Axiomatized :
        return StdMath.trunc(x)

    @staticmethod
    def tan(x: z3) -> Axiomatized :
        _ , s = StdMath.sin(x)
        _ , c = StdMath.cos(x)
        tan = Function("tan",RealSort(), RealSort())
        axioms = [
            c != 0,
            tan(x) == s(x)/c(x) 
        ]
        return axioms, tan(x)

    @staticmethod
    def ceil(x: z3) -> Axiomatized :
        ax, f = StdMath.floor(x)
        return ax, f + 1
    
    @staticmethod
    def sqrt(x: z3) -> Axiomatized :
        f = Function("sqrt", RealSort(), RealSort())
        x,y = Real("x"), Real("y")
        axioms = [
            x > 0,
            f(x) > 0,
            (f(x) == y) == (y**2 == x)
        ]
        return axioms, f(x)
    
    @staticmethod
    def cbrt(x: z3) -> Axiomatized :
        f = Function("cbrt", RealSort(), RealSort())
        y = Real("y")
        axioms = [
            (f(x) == y) == (y**3 == x)
        ]
        return axioms, f(x)

    @staticmethod
    def cosh(x: z3) -> Axiomatized :
        f = Function("cosh",RealSort(),RealSort())
        ax, ex = StdMath.exp(x)
        ax += [
            f(0) == 1,
            f(x) == (ex(x) + ex(-1*x))/2
        ]
        return ax, f(x)

    @staticmethod
    def sinh(x: z3) -> Axiomatized :
        f = Function("sinh",RealSort(),RealSort())
        ax, ex = StdMath.exp(x)
        ax += [
            f(0) == 0,
            f(x) == (ex(x) - ex(-1*x))/2
        ]
        return ax, f(x)
    
    @staticmethod
    def tanh(x: z3) -> Axiomatized :
        s_ax , sh = StdMath.sinh(x)
        c_ax , ch = StdMath.cosh(x)
        tanh = Function("tanh",RealSort(), RealSort())
        axioms = s_ax + c_ax + [
            ch != 0,
            tanh(x) == sh(x)/ch(x) 
        ]
        return axioms, tanh(x)

    @staticmethod
    def log(x: z3) -> Axiomatized :
        f = Function("log",RealSort(), RealSort())
        y = Real("y")
        axioms = [
            x > 0,
            f(1) == 0,
            (f(x) == y) == (StdMath.e ** y == x) 
        ]
        return axioms, f(x)

    @staticmethod
    def log1p(x: z3) -> Axiomatized :
        return StdMath.log(1+x)
    
    @staticmethod
    def log10(x: z3) -> Axiomatized :
        f = Function("log10",RealSort(), RealSort())
        y = Real("y")
        axioms = [
            x > 0,
            f(1) == 0,
            (f(x) == y) == (10 ** y == x) 
        ]
        return axioms, f(x)
    
    @staticmethod
    def log2(x: z3) -> Axiomatized :
        f = Function("log2",RealSort(), RealSort())
        y = Real("y")
        axioms = [
            x > 0,
            f(1) == 0,
            (f(x) == y) == (2 ** y == x) 
        ]
        return axioms, f(x)

    @staticmethod
    def pow(x: z3, y: z3) -> Axiomatized :
        f = Function("pow",RealSort(), RealSort(), RealSort())
        axioms = [
            Or(x != 0,y != 0),
            f(x,y) == x ** y
        ]
        return axioms, f(x,y)

    @staticmethod
    def asin(x: z3) -> Axiomatized :
        ax, s = StdMath.sin(x)
        f = Function("asin", RealSort(), RealSort())
        y = Real("y")
        axioms = ax + [
            (f(x) == y) == (s(y) == x)
        ]
        return axioms, f(x)
    
    @staticmethod
    def acos(x: z3) -> Axiomatized :
        ax, c = StdMath.cos(x)
        f = Function("acos", RealSort(), RealSort())
        y = Real("y")
        axioms = ax + [
            (f(x) == y) == (c(y) == x)
        ]
        return axioms, f(x)
    
    @staticmethod
    def atan(x: z3) -> Axiomatized :
        ax, t = StdMath.tan(x)
        f = Function("atan", RealSort(), RealSort())
        y = Real("y")
        axioms = ax + [
            (f(x) == y) == (t(y) == x)
        ]
        return axioms, f(x)
    
    @staticmethod
    def asinh(x: z3) -> Axiomatized :
        ax, s = StdMath.sinh(x)
        f = Function("asinh", RealSort(), RealSort())
        y = Real("y")
        axioms = ax + [
            (f(x) == y) == (s(y) == x)
        ]
        return axioms, f(x)
    
    @staticmethod
    def acosh(x: z3) -> Axiomatized :
        ax, c = StdMath.cosh(x)
        f = Function("acosh", RealSort(), RealSort())
        y = Real("y")
        axioms = ax + [
            (f(x) == y) == (c(y) == x)
        ]
        return axioms, f(x)
    
    @staticmethod
    def atanh(x: z3) -> Axiomatized :
        ax, t = StdMath.tanh(x)
        f = Function("atanh", RealSort(), RealSort())
        y = Real("y")
        axioms = ax + [
            (f(x) == y) == (t(y) == x)
        ]
        return axioms, f(x)
    
    @staticmethod
    def atan2(x: z3, y: z3) -> Axiomatized :
        return StdMath.tanh(x/y)
