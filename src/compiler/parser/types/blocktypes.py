from enum import Enum

class Block(Enum) :
    function = 0
    loop = 1
    declaration = 2
    assignment = 3
    conditional = 4