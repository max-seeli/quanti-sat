from __future__ import annotations

from itertools import product
from typing import Dict, List, Tuple

import sympy as sp

from quantifier import Exists, ForAll, Quantifier


def convert(quantified_formula: Quantifier, degree: int, output: str = None) -> str:
    """
    Convert a quantified formula to an SMT2 formula.

    Parameters
    ----------
    quantified_formula : Quantifier
        The quantified formula to be converted.
    degree : int
        The degree of the polynomial templates.
    output : str, optional
        The file to save the SMT2 formula, by default None.

    Returns
    -------
    str
        The SMT2 formula.
    """
    all_quantified_vars, substitutions, formula = extract_2(quantified_formula, degree)
    formula = formula.subs(substitutions)
    free_variables = set(formula.free_symbols) - set(all_quantified_vars)

    smt2 = generate_smt2(list(free_variables), all_quantified_vars, formula)

    if output is not None:
        with open(output, 'w') as f:
            f.write(smt2)
    return smt2

def extract_1(quantified_formula: Quantifier, degree: int) -> Tuple[List[sp.Symbol], Dict[sp.Symbol, sp.Basic], sp.Basic]:
    """
    Extract the quantified variables and the substitutions from a quantified formula.
    
    Veriables with an *exists* quantifier will be replaced by a linear expression
    over all previous variables (to the left).

    Parameters
    ----------
    quantified_formula : Quantifier
        The quantified formula to extract the variables and substitutions.
    degree : int
        The degree of the polynomial expressions.
        
    Returns
    -------
    all_quantified_vars : List[sp.Symbol]
        The list of all quantified variables.
    substitutions : Dict[sp.Symbol, sp.Basic]
        The dictionary of substitutions.
        formula : sp.Basic
        The formula without quantifiers.
    """
    vars = []
    all_quantified_vars = []
    substitutions = {}

    counter = 0
    while isinstance(quantified_formula, Quantifier):
        if isinstance(quantified_formula, ForAll):
            vars.extend(quantified_formula.variables)
            all_quantified_vars.extend(quantified_formula.variables)
        elif isinstance(quantified_formula, Exists):
            exists_vars = quantified_formula.variables
            sub_dict = {var: get_polynomial_expression(f'a_{counter}_{i}', vars, degree) for i, var in enumerate(exists_vars)}
            vars.extend(exists_vars)

            for prev_var, prev_expr in substitutions.items():
                for var, expr in sub_dict.items():
                    sub_dict[var] = expr.subs(prev_var, prev_expr)

            substitutions.update(sub_dict)
            counter += 1
        quantified_formula = quantified_formula.formula

    return all_quantified_vars, substitutions, quantified_formula

def extract_2(quantified_formula: Quantifier, degree: int) -> Tuple[List[sp.Symbol], Dict[sp.Symbol, sp.Basic], sp.Basic]:
    """
    Extract the quantified variables and the substitutions from a quantified formula.
    
    Veriables with an *exists* quantifier will be replaced by a linear expression
    over all previous *forall*-quantified variables (to the left).

    Parameters
    ----------
    quantified_formula : Quantifier
        The quantified formula to extract the variables and substitutions.
    degree : int
        The degree of the polynomial expressions.
        
    Returns
    -------
    all_quantified_vars : List[sp.Symbol]
        The list of all quantified variables.
    substitutions : Dict[sp.Symbol, sp.Basic]
        The dictionary of substitutions.
        formula : sp.Basic
        The formula without quantifiers.
    """
    all_quantified_vars = []
    substitutions = {}

    counter = 0
    while isinstance(quantified_formula, Quantifier):
        if isinstance(quantified_formula, ForAll):
            all_quantified_vars.extend(quantified_formula.variables)
        elif isinstance(quantified_formula, Exists):
            exists_vars = quantified_formula.variables
            sub_dict = {var: get_polynomial_expression(f'a_{counter}_{i}', all_quantified_vars, degree) for i, var in enumerate(exists_vars)}
            substitutions.update(sub_dict)
            counter += 1
        quantified_formula = quantified_formula.formula

    return all_quantified_vars, substitutions, quantified_formula

def generate_smt2(free_vars: List[sp.Symbol], all_quantified_vars: List[sp.Symbol], formula: sp.Basic) -> str:

    smt_lines = []

    for var in free_vars:
        smt_lines.append(f'(declare-const {var.name} Real)')

    forall_vars = [f'({var.name} Real)' for var in all_quantified_vars]
    forall_vars = f"({' '.join(forall_vars)})"

    smt_formula = to_smt(formula)

    smt_lines.append(f'(assert (forall {forall_vars} (=> (> 1 0) {smt_formula})))')
    smt_lines.append('(check-sat)')
    smt_lines.append('(get-model)')

    return '\n'.join(smt_lines)

def get_linear_expression(coeffs_name: str, variables: List[sp.Symbol]) -> sp.Expr:
        """
        Get a linear expression given the coefficients and the variables.

        Parameters
        ----------
        coeffs_name : str
            The name of the coefficients.
        variables : List[sp.Symbol]
            The variables of the linear expression.

        Returns
        -------
        sp.Expr
            The linear expression.
        """
        coeffs = [sp.Symbol(f'{coeffs_name}_{i}') for i in range(len(variables) + 1)]
        return coeffs[0] + sum([coeff * variable for variable, coeff in zip(variables, coeffs[1:])])

def get_polynomial_expression(coeffs_name: str, variables: List[sp.Symbol], degree: int) -> sp.Expr:
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
    monomials = get_all_monomials(variables, degree)
    coeffs = [sp.Symbol(f'{coeffs_name}_{i}') for i in range(len(monomials))]
    return sum([coeff * monomial for coeff, monomial in zip(coeffs, monomials)])

def get_all_monomials(variables: List[sp.Symbol], degree: int) -> List[sp.Expr]:
    """
    Get all monomials of a given degree.

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
    for exponents in product(range(degree + 1), repeat=len(variables)):
        if sum(exponents) <= degree:
            monomials.append(sp.prod([variable**exponent for variable, exponent in zip(variables, exponents)]))
    return monomials

def to_smt(constraint: sp.Basic) -> str:
    """
    Convert a constraint to an SMT2 string.
    Parameters
    ----------
    constraint : sp.Basic
        The constraint to be converted.
    Returns
    -------
    str
        The SMT2 string representing the constraint.
    """
    if constraint.is_Relational:
        arg_pair = f'{to_smt(constraint.lhs)} {to_smt(constraint.rhs)}'
        if constraint.rel_op == '==':
            # PolyHorn Bug
            return f'(and (<= {arg_pair}) (>= {arg_pair}))'
        else:
            return f'({constraint.rel_op} {arg_pair})'
    elif constraint.is_Add:
        return f'(+ {" ".join([to_smt(arg) for arg in constraint.args])})'
    elif constraint.is_Mul:
        return f'(* {" ".join([to_smt(arg) for arg in constraint.args])})'
    elif constraint.is_Pow:
        return f'(* {" ".join([to_smt(constraint.base)] * int(constraint.exp))})'
    elif constraint.is_Function and constraint.is_Boolean:
        f = str(constraint.func).lower()
        if f == 'not':
            assert len(constraint.args) == 1, f'Expected 1 argument, got {len(constraint.args)}'
            child = constraint.args[0]
            if isinstance(child, sp.Implies):
                return f'(and {to_smt(child.args[0])} {to_smt(sp.Not(child.args[1]))})'
            elif isinstance(child, sp.And):
                return f'(or {to_smt(sp.Not(child.args[0]))} {to_smt(sp.Not(child.args[1]))})'
            elif isinstance(child, sp.Or):
                return f'(and {to_smt(sp.Not(child.args[0]))} {to_smt(sp.Not(child.args[1]))})'
            else:
                assert False, f'Unable to reduce negation on: {type(child)}'
        if f == 'implies':
            assert len(constraint.args) == 2, f'Expected 2 arguments, got {len(constraint.args)}'
            return f'(or {to_smt(sp.Not(constraint.args[0]))} {to_smt(constraint.args[1])})'
        return f'({str(constraint.func).lower()} {" ".join([to_smt(arg) for arg in constraint.args])})'
    elif isinstance(constraint, sp.UnevaluatedExpr):
        return to_smt(constraint.args[0])
    elif constraint.is_Symbol:
        return constraint.name
    elif constraint.is_Number:
        return str(constraint)
    elif constraint == sp.true:
        return 'true'
    elif constraint == sp.false:
        return 'false'
    else:
        raise ValueError(f'Unsupported constraint type: {type(constraint)}\n\tFor constraint: {constraint}')
