from lmb.structures import Body
from enum import Enum

class Mode(Enum) :
    detect_unreachable   = 0x00
    post_conditions_only = 0x01
    post_conditions_full = 0x02

class Runtime :

    def __init__(self, body: Body) -> None : ...