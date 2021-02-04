from enum import Enum 

class Language(Enum) :
    Javascript = 0x00

class ExprKind(Enum) :
    binary     = 0x00
    assignment = 0x01
    update     = 0x02
    unary      = 0x03

class Types(Enum) :
    null      = 0x00
    undefined = 0x01