from enum import Enum 

class Language(Enum) :
    Javascript = 0x00

class ExprKind(Enum) :
    binary     = 0x00
    assignment = 0x01
    update     = 0x02