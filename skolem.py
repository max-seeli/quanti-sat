import time
from enum import Enum
from typing import Dict, List, Tuple
import os

import sympy as sp

from expression import get_polynomial_expression
from quantifier import Exists, ForAll, Quantifier
from util import to_smt, set_timeout

class Result(Enum):
    CORRECT = 1
    INCORRECT = 2
    CONVERSION_TIMEOUT = 3
    SOLVER_TIMEOUT = 4
    PARSING_ERROR = 5
    BUG = 6
    BUG2 = 7

def skolemize(quantified_formula: Quantifier, use_template: bool, degree: int, output: str = None) -> str:
    """
    Convert a quantified formula to a skolemized formula.

    Parameters
    ----------
    quantified_formula : Quantifier
        The quantified formula to be converted.
    use_template : bool
        Use the template for the Skolem function.
    output : str, optional
        The file to save the SMT2 formula, by default None.

    Returns
    -------
    str
        The SMT2 formula.
    """
    all_quantified_vars, exists_vars, exists_forall_predecessors, formula = extract(quantified_formula)
    
    subs = {var: ExistVar(var.name) for var in exists_vars}
    for var in exists_vars:
        subs[var].predecessors = exists_forall_predecessors[var]
    
    formula = formula.subs(subs)

    smt2 = generate_smt2(formula, all_quantified_vars, exists_vars, exists_forall_predecessors, use_template, degree)

    if output is not None:
        with open(output, 'w') as f:
            f.write(smt2)
    return smt2


def extract(quantified_formula: Quantifier) -> Tuple[List[sp.Symbol], Dict[sp.Symbol, sp.Basic], sp.Basic]:
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
    exists_quantified_vars : List[sp.Symbol]
        The list of all variables with an *exists* quantifier.
    exists_forall_predecessors : Dict[sp.Symbol, List[sp.Symbol]]
        The list of all *forall* quantified variables for each *exists* quantified variable.
    formula : sp.Basic
        The formula without quantifiers.
    """
    all_quantified_vars = []
    exists_vars = []
    exists_forall_predecessors = {}

    while isinstance(quantified_formula, Quantifier):
        if isinstance(quantified_formula, ForAll):
            all_quantified_vars.extend(quantified_formula.variables)
        elif isinstance(quantified_formula, Exists):
            exists_vars.extend(quantified_formula.variables) 
            for var in quantified_formula.variables:
                exists_forall_predecessors[var] = all_quantified_vars.copy()   
        quantified_formula = quantified_formula.formula

    return all_quantified_vars, exists_vars, exists_forall_predecessors, quantified_formula


class ExistVar(sp.Symbol):

    def __init__(self, name: str):        
        self.name = name
        self.predecessors = None

    def __repr__(self):
        if len(self.predecessors) > 0:
            return f'({self.name} {" ".join([p.name for p in self.predecessors])})'
        else:
            return self.name

    def __str__(self):
        return self.__repr__()

def generate_smt2(formula: sp.Basic, all_quantified_vars: List[sp.Symbol], exists_vars: List[sp.Symbol], exists_forall_predecessors: Dict[sp.Symbol, List[sp.Symbol]], use_template: bool, degree: int) -> str:

    smt_lines = []

    if not use_template:
        for var in exists_vars:
            smt_lines.append(f'(declare-fun {var.name} ({" ".join(["Real"] * len(exists_forall_predecessors[var]))}) Real)')
    else:
        for i, var in enumerate(exists_vars):
            predecessors = exists_forall_predecessors[var]
            poly_expr = get_polynomial_expression(f"b_{i}", predecessors, degree)
            coeffs = set(poly_expr.free_symbols) - set(predecessors)
            for coeff in coeffs:
                smt_lines.append(f'(declare-const {coeff.name} Real)')
            
            formula = formula.subs(ExistVar(var.name), poly_expr)
    

    forall_vars = [f'({var.name} Real)' for var in all_quantified_vars]
    forall_vars = f"({' '.join(forall_vars)})"

    smt_formula = to_smt(formula)

    smt_lines.append(f'(assert (forall {forall_vars} (=> (>= 1 0) {smt_formula})))')
    smt_lines.append('(check-sat)')
    smt_lines.append('(get-model)')

    return '\n'.join(smt_lines)


if __name__ == "__main__":
    import os
    from argparse import ArgumentParser
    from parser.formula_parser import parse_file

    from z3solver import SAT2

    parser = ArgumentParser()
    parser.add_argument('--file', type=str, help='The file containing the quantified formula.')
    parser.add_argument('--use-template', action='store_true', help='Use the template for the Skolem function.')
    parser.add_argument('--degree', type=int, default=1, help='The degree of the polynomial expressions. (Only used if --use-template is set)')
    parser.add_argument('--output', type=str, help='The file to save the SMT2 formula.')
    parser.add_argument('--timeout', type=int, default=30, help='The timeout for the solver.')
    args = parser.parse_args()

    file = args.file

    conversion_time = None
    solving_time = None

    quantified_formula = parse_file(file) #os.path.join(args.folder, file))
    if quantified_formula is None:
        result = Result.PARSING_ERROR
    else:
        print("Quantified formula:")
        print(quantified_formula)
        
        qf = quantified_formula
        nqf = quantified_formula.negate()

        try:
            qf_conversion_start = time.time()
            qf_smt2 = set_timeout(skolemize, args.timeout, qf, args.use_template, degree=args.degree, output=args.output)
            qfconversion_time = time.time() - qf_conversion_start

            nqf_conversion_start = time.time()
            nqf_smt2 = set_timeout(skolemize, args.timeout, nqf, args.use_template, degree=args.degree, output=args.output)
            nqf_conversion_time = time.time() - nqf_conversion_start

            conversion_time = (qfconversion_time + nqf_conversion_time) / 2
        except TimeoutError:
            result = Result.CONVERSION_TIMEOUT
        else:
                      
            print("Converted formula:")
            print(qf_smt2)

            qf_solving_start = time.time()
            qf_result = SAT2(qf_smt2, timeout=args.timeout)
            qf_solving_time = time.time() - qf_solving_start

            nqf_solving_start = time.time()
            nqf_result = SAT2(nqf_smt2, timeout=args.timeout)
            nqf_solving_time = time.time() - nqf_solving_start

            solving_time = (qf_solving_time + nqf_solving_time) / 2

            if qf_result is None or nqf_result is None:
                result = Result.SOLVER_TIMEOUT
            else:
                qf_is_sat, qf_model = qf_result
                nqf_is_sat, nqf_model = nqf_result

                if qf_is_sat and nqf_is_sat:
                    result = Result.BUG
                elif (qf_is_sat and not nqf_is_sat) or (not qf_is_sat and nqf_is_sat):
                    result = Result.CORRECT
                elif not qf_is_sat and not nqf_is_sat:
                    result = Result.INCORRECT
                else:
                    result = Result.BUG2
            
                print('Model:')
                for var, value in qf_model.items():
                    print(f"{var}: {value}")


    print("Result:")
    match result:
        case Result.CORRECT:
            print('The formula was solved CORRECTLY.')
        case Result.INCORRECT:
            print('The formula was solved INCORRECTLY.')
        case Result.CONVERSION_TIMEOUT:
            print('The formula could not be converted due to timeout.')
        case Result.SOLVER_TIMEOUT:
            print('The formula could not be solved due to timeout.')
        case Result.PARSING_ERROR:
            print('The formula could not be parsed.')
        case Result.BUG:
            print('There is a BUG.')
        case Result.BUG2:
            print('There is a BUG2.')
        case _:
            raise ValueError('The experiment needs to be run before getting the result message.')

    print("CSV:")
    print(f"{os.path.basename(file)},{result.name},{conversion_time},{solving_time}")

