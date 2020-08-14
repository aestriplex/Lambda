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
        super().__init__(f"{_t.__name__} must inherits from `Instruction`.")

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
        super().__init__(f"Variable {_n} must be delacred in the context.")

class InvalidEntryPointException(Exception) :

    def __init__(self) :
        super().__init__("The entry point must be in the body.")