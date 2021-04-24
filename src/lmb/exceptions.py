class DepthTypeException(Exception) :
    
    def __init__(self,_t) :
        super().__init__(f"Depth must be an integer, not {_t.__name__}.")

class BodyTypeException(Exception) :
    
    def __init__(self,_t) :
        super().__init__(f"Depth must be a list, not {_t.__name__}.")

class ScriptTypeException(Exception) :
    
    def __init__(self,_t) :
        super().__init__(f"Script parameter must be an esprima.nodes.Script, not {_t.__name__}.")

class VarTypeException(Exception) :
    
    def __init__(self,_t) :
        super().__init__(f"You must pass a string for parameter {_t.__name__} insted of {type(_t).__name__}.")

class KindTypeException(Exception) :
    
    def __init__(self) :
        super().__init__(f"Kind unknown.")

class TypeException(Exception) :

    def __init__(self,_t) :
        super().__init__(f"{_t.__name__} must inherits from `Exe`.")

class UnsupportedOperatorException(Exception) :

    def __init__(self,o) :
        super().__init__(f"{o} is not supported.")
    
class UnsupportedTypeException(Exception) :

    def __init__(self,_t) :
        super().__init__(f"Type {_t} is not supported.")

class InnerContextMissingException(Exception) :

    def __init__(self) :
        super().__init__("In order to process binary expression, you have to specify an inner context (default none).")

class VariableMissingException(Exception) :

    def __init__(self,_n) :
        super().__init__(f"Variable `{_n}` must be delacred in the context.")

class InvalidEntryPointException(Exception) :

    def __init__(self) :
        super().__init__("The entry point must be in the body and it must be a function.")
    
class ImplicitlyTypedException(Exception) :

    def __init__(self, name) :
        super().__init__(f"Variable {name} is not declared in context. An undeclared variable cannot be implicitly typed.")

class BaseTypeException(Exception) :

    def __init__(self, var) :
        super().__init__(f"Base type must be a either a Variable or a Value, not a {type(var)}.")

class InconsistentTypeExpression(Exception) :

    def __init__(self, expr) :
        expr_str = f"{expr.get_first()} {expr.get_operator()} {expr.get_second()}"
        super().__init__(f"In expression `{expr_str}` types are incostistent.")

class InconsistentTypeAssignment(Exception) :

    def __init__(self, first, second) :
        super().__init__(f"`{first}` and `{second}` assignments are inconsistent.")

class InvalidModeException(Exception) :

    def __init__(self) :
        super().__init__(f"You cannot set a post-condition in ``detect unreachable`` mode.")

class NullPointerException(Exception) :

    def __init__(self, lbl: str) :
        super().__init__(f"The variable `{lbl}` is not allocated.")

class SegmentationFaultException(Exception) :

    def __init__(self, addr: str) :
        super().__init__(f"The address `{addr}` isn't allocated.")

class CommandNotFoundException(Exception) :

    def __init__(self, cmd: str) :
        super().__init__(f"Command `{cmd}` does not exists.")

class CommandParseException(Exception) :

    def __init__(self, cmd: str) :
        super().__init__(f"An error occurred while parsing `{cmd}`. Command has to have the structure <cmd:val>.")

class MissingParamenterException(Exception) :

    def __init__(self, func: str, param: str) :
        super().__init__(f"The function `{func}` doesn't take `{param}` as parameter.")

class UnknownTypeException(Exception) :

    def __init__(self, t: str) :
        super().__init__(f"The type `{t}` isn't available for initialization.")

class InconsistentTypeException(Exception) :

    def __init__(self, v: str, t: str) :
        super().__init__(f"`{v}` has to be of type: `{t}`")