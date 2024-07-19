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

    @abstractmethod
    def count_quantified_vars(self):
        pass

    @abstractmethod
    def count_quantifier_depth(self):
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
    
    def count_quantified_vars(self):
        if isinstance(self.formula, Quantifier):
            num_forall_vars, num_exists_vars = self.formula.count_quantified_vars()
            return len(self.variables) + num_forall_vars, num_exists_vars
        else:
            return len(self.variables), 0
        
    def count_quantifier_depth(self):
        if isinstance(self.formula, Exists):
            return 1 + self.formula.count_quantifier_depth()
        elif isinstance(self.formula, ForAll):
            return self.formula.count_quantifier_depth()
        else:
            return 1
    
    @property
    def free_symbols(self):
        result = []
        for s in self.formula.free_symbols:
            if s.name not in [v.name for v in self.variables]:
                result.append(s)

        return result

    
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
    
    def count_quantified_vars(self):
        if isinstance(self.formula, Quantifier):
            num_forall_vars, num_exists_vars = self.formula.count_quantified_vars()
            return num_forall_vars, len(self.variables) + num_exists_vars
        else:
            return 0, len(self.variables)
        
    def count_quantifier_depth(self):
        if isinstance(self.formula, ForAll):
            return 1 + self.formula.count_quantifier_depth()
        elif isinstance(self.formula, Exists):
            return self.formula.count_quantifier_depth()
        else:
            return 1
    
    @property
    def free_symbols(self):
        result = []
        for s in self.formula.free_symbols:
            if s.name not in [v.name for v in self.variables]:
                result.append(s)

        return result