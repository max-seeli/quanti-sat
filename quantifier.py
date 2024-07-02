from abc import ABC, abstractmethod
from typing import List, Union
import sympy as sp

class Quantifier(ABC):

    @abstractmethod
    def negate(self):
        pass

    @abstractmethod
    def subs(self, *args, **kwargs):
        pass

    @property
    @abstractmethod
    def free_symbols(self):
        pass

class ForAll(Quantifier):

    def __init__(self, variables: List[sp.Symbol], formula: Union[sp.Basic, Quantifier]):
        self.variables: List[sp.Symbol] = variables
        self.formula: Union[sp.Basic, Quantifier] = formula

    def __repr__(self):
        return f'Forall {", ".join([v.name for v in self.variables])}: {self.formula}'
    
    def negate(self):
        if isinstance(self.formula, Quantifier):
            return Exists(self.variables, self.formula.negate())
        else:
            return Exists(self.variables, sp.Not(self.formula))

    def subs(self, *args, **kwargs):
        return ForAll(self.variables, self.formula.subs(*args, **kwargs))
    
    @property
    def free_symbols(self):
        return self.formula.free_symbols - set(self.variables)

    
class Exists(Quantifier):

    def __init__(self, variables: List[sp.Symbol], formula: Union[sp.Basic, Quantifier]):
        self.variables: List[sp.Symbol] = variables
        self.formula: Union[sp.Basic, Quantifier] = formula

    def __repr__(self):
        return f'Exists {", ".join([v.name for v in self.variables])}: {self.formula}'
    
    def negate(self):
        if isinstance(self.formula, Quantifier):
            return ForAll(self.variables, self.formula.negate())
        else:
            return ForAll(self.variables, sp.Not(self.formula))

    def subs(self, *args, **kwargs):
        return Exists(self.variables, self.formula.subs(*args, **kwargs))
    
    @property
    def free_symbols(self):
        return self.formula.free_symbols - set(self.variables)