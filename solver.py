from abc import ABC, abstractmethod
from typing import Dict, List, Tuple

import sympy as sp

from converter import GenerationVariant, convert
from expression import get_polynomial_expression
from PolyHorn.src.main import execute_smt2
from quantifier import Exists, ForAll, Quantifier
from util import to_smt
from z3solver import SAT2


class Solver(ABC):
    
    @abstractmethod
    def convert(self):
        pass

    @abstractmethod
    def solve(self):
        pass


class QuantiSAT(Solver):

    def __init__(self, quantified_formula: Quantifier, args: dict):
        self.quantified_formula = quantified_formula
        self.degree = args.degree
        self.output = args.output
        self.polyhorn_config = args.config

        self.smt2 = None

    def convert(self):
        self.smt2 = convert(self.quantified_formula, degree=self.degree, variant=GenerationVariant.FORALL_ONLY)

        if self.output is not None:
            with open(self.output, 'w') as f:
                f.write(self.smt2)

        return self.smt2

    def solve(self):
        if self.smt2 is None:
            raise ValueError('The formula has not been converted yet.')
        
        return execute_smt2(self.polyhorn_config, self.smt2)


class Skolem(Solver):

    def __init__(self, quantified_formula: Quantifier, args: dict):
        self.quantified_formula = quantified_formula
        self.use_template = args.use_template
        self.degree = args.degree
        self.timeout = args.timeout
        self.output = args.output

        self.smt2 = None

    def convert(self) -> str:
        forall_vars, exists_predecessors, formula = self.__extract(self.quantified_formula)
        formula = self.__replace_exists_with_functions(formula, exists_predecessors)
        self.smt2 = self.__generate_smt2(formula, forall_vars, exists_predecessors)

        if self.output is not None:
            with open(self.output, 'w') as f:
                f.write(self.smt2)

        return self.smt2

    def solve(self):
        if self.smt2 is None:
            raise ValueError('The formula has not been converted yet.')
        return SAT2(self.smt2, self.timeout)
    
    def __extract(self, qf: Quantifier) -> Tuple[List[sp.Symbol], Dict[sp.Symbol, List[sp.Symbol]], sp.Basic]:
        """
        Extract the quantified variables and the substitutions from a quantified formula.

        Veriables with an *exists* quantifier will be replaced by a linear expression
        over all previous *forall*-quantified variables (to the left).

        Parameters
        ----------
        qf : Quantifier
            The quantified formula to extract the variables and substitutions.

        Returns
        -------
        forall_vars : List[sp.Symbol]
            The list of *forall* quantified variables.
        exists_predecessors : Dict[sp.Symbol, List[sp.Symbol]]
            The predecessors of each *exists* quantified variable.
        formula : sp.Basic
            The formula without quantifiers.
        """
        forall_vars, exists_predecessors = [], {}

        while isinstance(qf, Quantifier):
            if isinstance(qf, ForAll):
                forall_vars.extend(qf.variables)
            elif isinstance(qf, Exists):
                for var in qf.variables:
                    exists_predecessors[var] = forall_vars.copy()   
            qf = qf.formula

        return forall_vars, exists_predecessors, qf

    def __replace_exists_with_functions(self, formula: sp.Basic, exists_predecessors: Dict[sp.Symbol, List[sp.Symbol]]) -> sp.Basic:
        """
        Replace the *exists* quantified variables with functions of the predecessors.

        Parameters
        ----------
        formula : sp.Basic
            The formula to replace the *exists* quantified variables.
        exists_predecessors : Dict[sp.Symbol, List[sp.Symbol]]
            The predecessors of each *exists* quantified variable.

        Returns
        -------
        sp.Basic
            The formula with the *exists* quantified variables replaced by a linear expression.
        """
        for exists_var, predecessors in exists_predecessors.items():
            if self.use_template:
                expr = get_polynomial_expression(exists_var.name, predecessors, self.degree)
            else:
                expr = sp.Function(exists_var.name)(*predecessors)
            formula = formula.subs(exists_var, expr)
        return formula
    
    def __generate_smt2(self, formula: sp.Basic, forall_vars: List[sp.Symbol], exists_predecessors: Dict[sp.Symbol, List[sp.Symbol]]) -> str:

        smt_lines = []

        if self.use_template:
            coefficients = set(formula.free_symbols) - set(forall_vars)
            for coeff in coefficients:
                smt_lines.append(f'(declare-const {coeff.name} Real)')
        else:
            for exists_var, predecessor, in exists_predecessors.items():
                smt_lines.append(f'(declare-fun {exists_var.name} ({" ".join(["Real"] * len(predecessor))}) Real)')

        forall_format = ' '.join([f'({var.name} Real)' for var in forall_vars])

        smt_lines.append(f'(assert (forall ({forall_format}) (=> (>= 1 0) {to_smt(formula)})))')
        smt_lines.append('(check-sat)')
        smt_lines.append('(get-model)')

        return '\n'.join(smt_lines)
