from argparse import ArgumentParser

import regex as re
import sympy as sp

from io import StringIO
from pysmt.smtlib.parser import SmtLibParser 

from quantifier import Exists, ForAll, Quantifier


def parse_file(file_path):
    
    with open(file_path, 'r') as file:
        content = file.read()

    parser = SmtLibParser()

    with StringIO(content) as stream:
        script = parser.get_script(stream)

    f = script.get_last_formula()
    converted_f: Quantifier = from_pysmt(f)

    free_symbols = converted_f.free_symbols
    if len(free_symbols) > 0:
        converted_f = Exists(list(free_symbols), converted_f)

    converted_f = converted_f.negate() # For the unsat dataset to be consistent with our sat solver
    return converted_f



def from_pysmt(expr) -> Quantifier:
    """
    Convert a pysmt expression to a quantified formula.
    
    Parameters
    ----------
    expr : pysmt.fnode.FNode
        The expression to convert.
        
    Returns
    -------
    Quantifier
        The quantified formula.
    """
    if expr.is_forall():
        print(expr.args())
        assert False
    elif expr.is_exists():
        assert len(expr.args()) == 1, f'Expected 1 argument, got {len(expr.args())}'
        return Exists([sp.Symbol(var.symbol_name()) for var in expr.quantifier_vars()], from_pysmt(expr.arg(0)))
    elif expr.is_le():
        assert len(expr.args()) == 2, f'Expected 2 arguments, got {len(expr.args())}'
        return sp.Le(from_pysmt(expr.arg(0)), from_pysmt(expr.arg(1)))
    elif expr.is_lt():
        assert len(expr.args()) == 2, f'Expected 2 arguments, got {len(expr.args())}'
        return sp.Lt(from_pysmt(expr.arg(0)), from_pysmt(expr.arg(1)))
    elif expr.is_equals():
        assert len(expr.args()) == 2, f'Expected 2 arguments, got {len(expr.args())}'
        return sp.Eq(from_pysmt(expr.arg(0)), from_pysmt(expr.arg(1)))
    elif expr.is_implies():
        assert len(expr.args()) == 2, f'Expected 2 arguments, got {len(expr.args())}'
        return sp.Implies(from_pysmt(expr.arg(0)), from_pysmt(expr.arg(1)))
    elif expr.is_and():
        assert len(expr.args()) == 2, f'Expected 2 arguments, got {len(expr.args())}'
        return sp.And(from_pysmt(expr.arg(0)), from_pysmt(expr.arg(1)))
    elif expr.is_or():
        assert len(expr.args()) == 2, f'Expected 2 arguments, got {len(expr.args())}'
        return sp.Or(from_pysmt(expr.arg(0)), from_pysmt(expr.arg(1)))
    elif expr.is_not():
        assert len(expr.args()) == 1, f'Expected 1 argument, got {len(expr.args())}'

        child = from_pysmt(expr.arg(0))
        if isinstance(child, Quantifier):
            return child.negate()
        else:
            return sp.Not(child)
    elif expr.is_plus():
        assert len(expr.args()) == 2, f'Expected 2 arguments, got {len(expr.args())}'
        return sp.Add(from_pysmt(expr.arg(0)), from_pysmt(expr.arg(1)))
    elif expr.is_minus():
        assert len(expr.args()) == 2, f'Expected 2 arguments, got {len(expr.args())}'
        return sp.Add(from_pysmt(expr.arg(0)), -from_pysmt(expr.arg(1)))
    elif expr.is_times():
        assert len(expr.args()) == 2, f'Expected 2 arguments, got {len(expr.args())}'
        return sp.Mul(from_pysmt(expr.arg(0)), from_pysmt(expr.arg(1)))
    elif expr.is_constant():
        assert len(expr.args()) == 0, f'Expected 0 arguments, got {len(expr.args())}'
        assert expr.constant_value() is not None, f'Expected a constant value, got None'
        return sp.Number(float(expr.constant_value()))
    elif expr.is_symbol():
        assert len(expr.args()) == 0, f'Expected 0 arguments, got {len(expr.args())}'
        assert expr.symbol_name() is not None, f'Expected a symbol name, got None'
        return sp.Symbol(expr.symbol_name())
    else:
        raise ValueError(f'Unsupported expression type: {expr.node_type()} of expression {expr}')
