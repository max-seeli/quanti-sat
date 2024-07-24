import os

import numpy as np
import sympy as sp

from expression import get_polynomial_expression
from quantifier import Exists, ForAll
from util import split, to_smt


def generate_formula(num_variables, degree, num_conditions, num_quantifiers):
    """
    Generate a formula with the given number of variables, degree, conditions and quantifiers.

    Parameters
    ----------
    num_variables : int
        The number of variables.
    degree : int
        The degree of the polynomial.
    num_conditions : int
        The number of conditions.
    num_quantifiers : int
        The number of quantifiers.

    Returns
    -------
    sp.Basic
        The generated formula.
    """
    if num_quantifiers > num_variables:
        raise ValueError("The number of quantifiers must be less than or equal to the number of variables.")

    # Generate the variables
    x = sp.symbols(f'x:{num_variables}')

    # Generate ground part of the formula
    ground_formula = None
    for i in range(num_conditions):
        condition = get_polynomial_expression(f'c{i}', x, degree)
        coefficients = set(condition.free_symbols) - set(x)

        # Assign coefficients randomly
        coeff_values = np.round(np.random.uniform(-5, 6, len(coefficients)), 2)
        condition = condition.subs({coeff: coeff_value for coeff, coeff_value in zip(coefficients, coeff_values)})

        # Assign operator randomly
        operator = np.random.choice(['==', '!=', '<', '<=', '>', '>='])
        if ground_formula is None:
            ground_formula = sp.Rel(condition, 0, operator)
        else:
            ground_formula = sp.And(ground_formula, sp.Rel(condition, 0, operator))

    quantifiers = [Exists, ForAll]
    # Split the variables into sets of equal size (one for each quantifier)
    num_variables = split(x, num_quantifiers) 

    # Generate the quantified formula
    quantified_formula = ground_formula
    for i, q_vars in enumerate(num_variables):
        quantifier = quantifiers[i % 2] # Alternate between Exists and ForAll
        quantified_formula = quantifier(q_vars, quantified_formula)

    return quantified_formula



def generate_instance(num_variables, degree, num_conditions, num_quantifiers):
    """
    Generate an smt2 instance for a solver.

    Parameters
    ----------
    num_variables : int
        The number of variables.
    degree : int
        The degree of the polynomial.
    num_conditions : int
        The number of conditions.
    num_quantifiers : int
        The number of quantifiers.

    Returns
    -------
    str
        The smt2 instance.
    """
    formula = generate_formula(num_variables, degree, num_conditions, num_quantifiers)
    smt2_formula = to_smt(formula)

    smt2_instance = f'(assert {smt2_formula})\n(check-sat)\n(get-model)'

    return smt2_instance



def generate_benchmark(path, num_instances, num_variables, degree, num_conditions, num_quantifiers):
    """
    Generate a benchmark with the given number of instances.

    Parameters
    ----------
    path : str
        The folder to save the instances.
    num_instances : int
        The number of instances.
    num_variables : int
        The number of variables per instance.
    degree : int
        The degree of the polynomials.
    num_conditions : int
        The number of conditions per instance.
    num_quantifiers : int
        The number of quantifiers per instance.
    """
    if not os.path.exists(path):
        os.makedirs(path)

    highest_instance = -1
    for file in os.listdir(path):
        if file.startswith('instance_'):
            instance_number = int(file.split('_')[1].split('.')[0])
            if instance_number > highest_instance:
                highest_instance = instance_number
    highest_instance += 1

    for i in range(num_instances):
        instance = generate_instance(num_variables, degree, num_conditions, num_quantifiers)
            
        with open(os.path.join(path, f'instance_{highest_instance + i}.smt2'), 'w') as file:
            file.write(instance)


if __name__ == "__main__":
    for i in range(1, 11):
        generate_benchmark('benchmark', num_instances=10, num_variables=i, degree=1, num_conditions=1, num_quantifiers=i)

    