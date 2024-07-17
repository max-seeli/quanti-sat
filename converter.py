from __future__ import annotations

from itertools import product
from typing import Dict, List, Tuple
from abc import abstractmethod, ABC
from enum import Enum
from warnings import warn

import sympy as sp

from quantifier import Exists, ForAll, Quantifier
from util import to_smt


def convert(quantified_formula: Quantifier, degree: int, variant: GenerationVariant, output: str = None) -> str:
    """
    Convert a quantified formula to an SMT2 formula.

    Parameters
    ----------
    quantified_formula : Quantifier
        The quantified formula to be converted.
    degree : int
        The degree of the polynomial templates.
    variant : GenerationVariant, optional
        The generation variant of the SMT2 formula, by default GenerationVariant.FORALL_ONLY.
    output : str, optional
        The file to save the SMT2 formula, by default None.

    Returns
    -------
    str
        The SMT2 formula.
    """
    converter = Converter(degree, variant)
    return converter.convert(quantified_formula, output)

class GenerationVariant(Enum):
    """
    The generation variant of the SMT2 formula.

    FORALL_ONLY: The templates are expressions of the forall-quantified variables.
    FORALL_EXISTS: The templates are expressions of the forall-quantified variables and the exists-quantified variables.
    ASSERTIONS: The templates are asserted on the left side of the constraint pairs.
    """
    FORALL_ONLY = 0
    FORALL_EXISTS = 1
    ASSERTIONS = 2

class Converter:
    """
    The converter class to convert a quantified formula to an SMT2 formula.
    """
    def __init__(self, degree: int, variant: GenerationVariant = GenerationVariant.FORALL_ONLY):
        """
        Initialize the converter.

        Parameters
        ----------
        degree : int
            The degree of the polynomial templates.
        variant : GenerationVariant, optional
            The generation variant of the SMT2 formula, by default GenerationVariant.FORALL_ONLY.
        """
        self.degree = degree
        self.variant = variant

    def convert(self, quantified_formula: Quantifier, output: str = None) -> str:
        """
        Convert a quantified formula to an SMT2 formula.

        Parameters
        ----------
        quantified_formula : Quantifier
            The quantified formula to be converted.
        output : str, optional
            The file to save the SMT2 formula, by default None.

        Returns
        -------
        str
            The SMT2 formula.
        """
        extractor = Extractor.get_extractor(self.degree, self.variant)
        forall_quant_vars, template_subs, ground_formula, assertion = extractor.extract(quantified_formula)

        ground_formula = ground_formula.subs(template_subs)

        all_vars = set(ground_formula.free_symbols).union(set(assertion.free_symbols))
        free_vars = all_vars - set(forall_quant_vars)

        smt2 = self.generate_smt2(list(free_vars), forall_quant_vars, assertion, ground_formula)

        if output is not None:
            with open(output, 'w') as f:
                f.write(smt2)
        return smt2
    
    def generate_smt2(self, free_vars: List[sp.Symbol], forall_quant_vars: List[sp.Symbol], assertion: sp.Basic, ground_formula: sp.Basic) -> str:
        smt_lines = []

        for var in free_vars:
            smt_lines.append(f'(declare-const {var.name} Real)')

        forall_vars = [f'({var.name} Real)' for var in forall_quant_vars]
        forall_vars = f"({' '.join(forall_vars)})"



        #premise = to_smt(assertion)
        # Check if ground_formula is CNF
        #ground_formula = sp.to_cnf(ground_formula)
        
        #if isinstance(ground_formula, sp.And):
        if False:
            for clause in ground_formula.args:
                if isinstance(clause, sp.Or):
                    lhs = sp.And(*[sp.Not(arg) for arg in clause.args[:-1]])
                    rhs = clause.args[-1]
                    smt_lines.append(f'(assert (forall {forall_vars} (=> {to_smt(lhs)} {to_smt(rhs)})))')
                else:
                    smt_lines.append(f'(assert (forall {forall_vars} (=> (>= 1 0) {to_smt(clause)})))')
        else:
            smt_lines.append(f'(assert (forall {forall_vars} (=> (>= 1 0) {to_smt(ground_formula)})))')

        smt_lines.append('(check-sat)')
        smt_lines.append('(get-model)')

        return '\n'.join(smt_lines)

class Extractor(ABC):
    """
    The extractor class to extract the quantified variables and the substitutions from a quantified formula.

    Usage
    -----
    ```python
    extractor = Extractor.get_extractor(degree, variant)

    forall_quant_vars, template_subs, ground_formula, assertion = extractor.extract(quantified_formula)
    ```
    """

    _create_key = object()

    @classmethod
    def get_extractor(cls, degree: int, variant: GenerationVariant) -> Extractor:
        """
        Get an extractor.

        Parameters
        ----------
        degree : int
            The degree of the polynomial templates.
        variant : GenerationVariant
            The generation variant of the SMT2 formula.

        Returns
        -------
        Extractor
            The extractor.
        """
        match variant:
            case GenerationVariant.FORALL_ONLY:
                return ForallOnlyExtractor(degree)
            case GenerationVariant.FORALL_EXISTS:
                return ForallExistsExtractor(degree)
            case GenerationVariant.ASSERTIONS:
                raise ValueError("Currently not working")
                return AssertionsExtractor(degree)
            case _:
                raise ValueError(f'Unsupported generation variant: {variant}')

    def __init__(self, create_key: object, degree: int):
        """
        Initialize the extractor.

        Parameters
        ----------
        create_key : object
            The key to create the extractor.
        """
        if create_key is not Extractor._create_key:
            raise ValueError('Extractor cannot be instantiated directly. Use get_extractor(..) instead.')
        self.degree = degree
    
    @abstractmethod
    def extract(self, quantified_formula: Quantifier) -> Tuple[List[sp.Symbol], Dict[sp.Symbol, sp.Basic], sp.Basic]:
        """
        Extract information from a quantified formula such that we can construct constraints from it.

        Parameters
        ----------
        quantified_formula : Quantifier
            The quantified formula to extract the variables and substitutions.
            
        Returns
        -------
        forall_quant_vars : List[sp.Symbol]
            The list of forall-quantified variables.
        template_subs : Dict[sp.Symbol, sp.Basic]
            The dictionary of substitutions for the templates of the exists-quantified variables.
        ground_formula : sp.Basic
            The formula without quantifiers.
        assertion : sp.Basic
            Assertions to be added to the left side of the constraint pairs.
        """
        pass

    def get_polynomial_expression(self, coeffs_name: str, variables: List[sp.Symbol]) -> sp.Expr:
        """
        Get a polynomial expression given the coefficients and the variables.

        Parameters
        ----------
        coeffs_name : str
            The name of the coefficients.
        variables : List[sp.Symbol]
            The variables of the polynomial expression.
        degree : int
            The degree of the polynomial expression.

        Returns
        -------
        sp.Expr
            The polynomial expression.
        """
        monomials = self.get_all_monomials(variables)
        coeffs = [sp.Symbol(f'{coeffs_name}_{i}') for i in range(len(monomials))]
        return sum([coeff * monomial for coeff, monomial in zip(coeffs, monomials)])

    def get_all_monomials(self, variables: List[sp.Symbol]) -> List[sp.Expr]:
        """
        Get all monomials of a given degree over the variables.

        Parameters
        ----------
        variables : List[sp.Symbol]
            The variables of the monomials.
        degree : int
            The degree of the monomials.

        Returns
        -------
        List[sp.Expr]
            The list of monomials.
        """
        monomials = []
        for exponents in product(range(self.degree + 1), repeat=len(variables)):
            if sum(exponents) <= self.degree:
                monomials.append(sp.prod([variable**exponent for variable, exponent in zip(variables, exponents)]))
        return monomials



class ForallOnlyExtractor(Extractor):
    """
    The extractor for the FORALL_ONLY generation variant.
    """
    def __init__(self, degree: int):
        """
        Initialize the extractor.

        Parameters
        ----------
        degree : int
            The degree of the polynomial templates.
        """
        super().__init__(Extractor._create_key, degree)

    def extract(self, quantified_formula: Quantifier) -> Tuple[List[sp.Symbol], Dict[sp.Symbol, sp.Basic], sp.Basic]:
        """
        Extract information from a quantified formula such that we can construct constraints from it.

        Parameters
        ----------
        quantified_formula : Quantifier
            The quantified formula to extract the variables and substitutions.

        Returns
        -------
        forall_quant_vars : List[sp.Symbol]
            The list of forall-quantified variables.
        template_subs : Dict[sp.Symbol, sp.Basic]
            The dictionary of substitutions for the templates of the exists-quantified variables.
        ground_formula : sp.Basic
            The formula without quantifiers.
        assertion : sp.Basic
            Assertions to be added to the left side of the constraint pairs.
        """
        forall_quant_vars = []
        template_subs = {}

        counter = 0
        while isinstance(quantified_formula, Quantifier):
            if isinstance(quantified_formula, ForAll):
                forall_quant_vars.extend(quantified_formula.variables)
            elif isinstance(quantified_formula, Exists):
                exists_vars = quantified_formula.variables
                sub_dict = {var: self.get_polynomial_expression(f'a_{counter}_{i}', forall_quant_vars) for i, var in enumerate(exists_vars)}
                template_subs.update(sub_dict)
                counter += 1
            quantified_formula = quantified_formula.formula
        ground_formula = quantified_formula

        return forall_quant_vars, template_subs, ground_formula, sp.true


class ForallExistsExtractor(Extractor):
    """
    The extractor for the FORALL_EXISTS generation variant.
    """
    def __init__(self, degree: int):
        """
        Initialize the extractor.

        Parameters
        ----------
        degree : int
            The degree of the polynomial templates.
        """
        super().__init__(Extractor._create_key, degree)

    def extract(self, quantified_formula: Quantifier) -> Tuple[List[sp.Symbol], Dict[sp.Symbol, sp.Basic], sp.Basic]:
        """
        Extract information from a quantified formula such that we can construct constraints from it.

        Parameters
        ----------
        quantified_formula : Quantifier
            The quantified formula to extract the variables and substitutions.

        Returns
        -------
        forall_quant_vars : List[sp.Symbol]
            The list of forall-quantified variables.
        template_subs : Dict[sp.Symbol, sp.Basic]
            The dictionary of substitutions for the templates of the exists-quantified variables.
        ground_formula : sp.Basic
            The formula without quantifiers.
        assertion : sp.Basic
            Assertions to be added to the left side of the constraint pairs.
        """
        all_vars = []
        forall_quant_vars = []
        template_subs = {}

        counter = 0
        while isinstance(quantified_formula, Quantifier):
            if isinstance(quantified_formula, ForAll):
                all_vars.extend(quantified_formula.variables)
                forall_quant_vars.extend(quantified_formula.variables)
            elif isinstance(quantified_formula, Exists):
                all_vars.extend(quantified_formula.variables)
                sub_dict = {var: self.get_polynomial_expression(f'a_{counter}_{i}', all_vars) for i, var in enumerate(quantified_formula.variables)}

            for prev_var, prev_expr in template_subs.items():
                for var, expr in sub_dict.items():
                    sub_dict[var] = expr.subs(prev_var, prev_expr)

            template_subs.update(sub_dict)
            counter += 1
            quantified_formula = quantified_formula.formula
        ground_formula = quantified_formula

        return forall_quant_vars, template_subs, ground_formula, sp.true
   


class AssertionsExtractor(Extractor):
    """
    The extractor for the ASSERTIONS generation variant.
    """
    def __init__(self, degree: int):
        """
        Initialize the extractor.

        Parameters
        ----------
        degree : int
            The degree of the polynomial templates.
        """
        super().__init__(Extractor._create_key, degree)

    def extract(self, quantified_formula: Quantifier) -> Tuple[List[sp.Symbol], Dict[sp.Symbol, sp.Basic], sp.Basic]:
        """
        Extract information from a quantified formula such that we can construct constraints from it.

        Parameters
        ----------
        quantified_formula : Quantifier
            The quantified formula to extract the variables and substitutions.

        Returns
        -------
        forall_quant_vars : List[sp.Symbol]
            The list of forall-quantified variables.
        template_subs : Dict[sp.Symbol, sp.Basic]
            The dictionary of substitutions for the templates of the exists-quantified variables.
        ground_formula : sp.Basic
            The formula without quantifiers.
        assertion : sp.Basic
            Assertions to be added to the left side of the constraint pairs.
        """
        forall_quant_vars = []
        template_subs = {}

        counter = 0
        while isinstance(quantified_formula, Quantifier):
            if isinstance(quantified_formula, ForAll):
                forall_quant_vars.extend(quantified_formula.variables)
            elif isinstance(quantified_formula, Exists):
                sub_dict = {var: self.get_polynomial_expression(f'a_{counter}_{i}', forall_quant_vars) for i, var in enumerate(quantified_formula.variables)}
                template_subs.update(sub_dict)
                counter += 1
            quantified_formula = quantified_formula.formula
        ground_formula = quantified_formula

        assertions = []
        for var, expr in template_subs.items():
            assertions.append(sp.Eq(var, expr))
        assertion = sp.And(*assertions)
        return forall_quant_vars, {}, ground_formula, assertion
