from z3 import *
import sympy as sp
import quantifier as q

def SAT(formula: sp.Basic) -> bool:
    """
    Check if the formula is satisfiable.
    
    Parameters
    ----------
    formula : sp.Basic
        The formula to be checked.
        
    Returns
    -------
    bool
        True if the formula is satisfiable, False otherwise.
    """
    s = Solver()
    s.add(to_z3(formula))
    return s.check() == sat


def to_z3(expr: sp.Basic) -> z3.ExprRef:
    if isinstance(expr, sp.LessThan):
        return to_z3(expr.lhs) <= to_z3(expr.rhs)
    elif isinstance(expr, sp.StrictLessThan):
        return to_z3(expr.lhs) < to_z3(expr.rhs)
    elif isinstance(expr, sp.GreaterThan):
        return to_z3(expr.lhs) >= to_z3(expr.rhs)
    elif isinstance(expr, sp.StrictGreaterThan):
        return to_z3(expr.lhs) > to_z3(expr.rhs)
    elif isinstance(expr, sp.Eq):
        return to_z3(expr.lhs) == to_z3(expr.rhs)
    elif isinstance(expr, sp.And):
        return And([to_z3(arg) for arg in expr.args])
    elif isinstance(expr, sp.Or):
        return Or([to_z3(arg) for arg in expr.args])
    elif isinstance(expr, sp.Not):
        return Not(to_z3(expr.args[0]))
    elif isinstance(expr, sp.Add):
        return Sum([to_z3(arg) for arg in expr.args])
    elif isinstance(expr, sp.Mul):
        return Product([to_z3(arg) for arg in expr.args])
    elif isinstance(expr, sp.Abs):
        return Abs(to_z3(expr.args[0]))
    elif isinstance(expr, sp.Pow):
        return to_z3(expr.base) ** to_z3(expr.exp)
    elif isinstance(expr, sp.Number):
        return RealVal(expr)
    elif isinstance(expr, sp.UnevaluatedExpr):
        return to_z3(expr.args[0])
    elif isinstance(expr, sp.Symbol):
        return Real(expr.name)
    elif isinstance(expr, sp.logic.boolalg.BooleanTrue):
        return BoolVal(True)
    elif isinstance(expr, sp.logic.boolalg.BooleanFalse):
        return BoolVal(False)
    elif isinstance(expr, q.ForAll):
        return ForAll([to_z3(var) for var in expr.variables], to_z3(expr.formula))
    elif isinstance(expr, q.Exists):
        return Exists([to_z3(var) for var in expr.variables], to_z3(expr.formula))
    else:
        raise ValueError(f'Unsupported expression type: {type(expr)}')