class DepthTypeException(Exception) :
    
    def __init__(self,_t) :
        self.msg = f"Depth must be an integer, not {_t.__name__}"
    
    def __str__(self) :
        return self.msg

class BodyTypeException(Exception) :
    
    def __init__(self,_t) :
        self.msg = f"Depth must be a list, not {_t.__name__}"
    
    def __str__(self) :
        return self.msg

class ScriptTypeException(Exception) :
    
    def __init__(self,_t) :
        self.msg = f"Script parameter must be an esprima.nodes.Script, not {_t.__name__}"
    
    def __str__(self) :
        return self.msg

class VarTypeException(Exception) :
    
    def __init__(self,_t) :
        self.msg = f"You must pass a string for parameter {_t.__name__} insted of {type(_t).__name__}"
    
    def __str__(self) :
        return self.msg

class KindTypeException(Exception) :
    
    def __init__(self) :
        self.msg = f"Kind unknown"
    
    def __str__(self) :
        return self.msg

class TypeException(Exception) :

    def __init__(self,_t) :
        self.msg = f"{_t.__name__} must inherits from `Instruction`"
    
    def __str__(self) :
        return self.msg