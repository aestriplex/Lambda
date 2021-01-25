from .types import VarType
from lmb.settings import VarSettings

js_specifics = {
    VarType.array : VarSettings.reference,
    VarType.obj : VarSettings.reference,
    VarType.literal : VarSettings.value
    }