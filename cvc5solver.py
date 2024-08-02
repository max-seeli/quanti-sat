from typing import Tuple, Dict

import os
import subprocess
import regex as re

from util import set_timeout


def CVC5(formula: str, timeout: int) -> Tuple[bool, Dict[str, float]]:
    """
    Check if the formula is satisfiable.
    
    Parameters
    ----------
    formula : str
        The formula in smt2 to be checked.
    timeout : int
        The timeout in seconds.
        
    Returns
    -------
    bool
        True if the formula is satisfiable, False otherwise.
    Dict[str, float]
        The model.
    """

    # Replace all negative numbers with (- x)
    formula = re.sub(r'(?<!\w)-(\d+(\.\d+)?)', r'(- \g<1>)', formula)
    print(formula)

    # Start the process
    process = subprocess.Popen(['cvc5', '--lang=smt2', '--produce-models', '--tlimit=%d' % (timeout * 1000)],
                               stdin=subprocess.PIPE,
                               stdout=subprocess.PIPE,
                               stderr=subprocess.PIPE)
    # Write the formula to the process
    process.stdin.write(formula.encode())
    process.stdin.close()

    # Wait for the process to finish
    try:
        process.wait(timeout)
    except subprocess.TimeoutExpired:
        process.kill()
        return None, {}

    # Read the output
    output = process.stdout.read().decode()
    error = process.stderr.read().decode()

    print(output)
    # Check the result
    if 'unsat' in output:
        return False, {}
    elif 'sat' in output:
        model = {}
        for line in output.split('\n'):
            if line.startswith('(define-'):
                print(line)
                print(line.split(maxsplit=4))
                _, var, _, _, val = line.split(maxsplit=4)
                model[var] = val
        return True, model
    else:
        return None, {}


    """
    with smt.Solver(name='cvc5', logic="nra") as solver:
        #solver.set_timeout(timeout)
        parser = SmtLibParser(Environment())
        with StringIO(formula) as stream:
            script = parser.get_script(stream)
        f = script.get_last_formula()
        solver.add_assertion(f)
        try:
            result = set_timeout(solver.solve, timeout)
        except (SolverReturnedUnknownResultError, TimeoutError):
            result = None

        print("Result", result)
        if result == True:
            model = solver.get_model()
            # convert model to dict
            
            model = {var: val for var, val in model}
                
            return True, model
        elif result == False:
            return False, {}
        else:
            return None, {}
        """
        

if __name__ == "__main__":

    with open('out.smt2', 'r') as f:
        formula = f.read()

    print(CVC5("""
(declare-fun v4 (Real) Real)
(declare-fun v2 (Real Real) Real)
(declare-fun v0 (Real Real Real) Real)
(assert (forall ((v1 Real) (v3 Real) (v5 Real)) (=> (<= 0.0 1.0) (and (<= (+ (* -8.0 v1) (* -2.0 v3) (* 6.0 v5)) -9.0) (<= (+ (* -13.0 (v0 v1 v3 v5)) (* 8.0 v3) (* 8.0 (v2 v3 v5)) (* 11.0 (v4 v5))) 0.0) (or (<= (+ (* -1.0 v3) (* 3.0 (v2 v3 v5)) (* 4.0 v1) (* 9.0 (v4 v5))) -3.0) (and (<= (+ (* -1.0 v1) (* -10.0 v5) (* -7.0 (v2 v3 v5))) 9.0) (<= (+ (* -12.0 v1) (* 4.0 (v4 v5)) (* 9.0 v5) (* 9.0 (v2 v3 v5))) -4.0))) (or (and (<= (+ v3 (* -11.0 v1) (* -8.0 v5)) -9.0) (<= (+ (* -1.0 (v0 v1 v3 v5)) (* -7.0 (v2 v3 v5)) (* -2.0 v1) (* -2.0 (v4 v5))) -5.0)) (and (<= (+ (* -1.0 (v4 v5)) (* -5.0 v1) (* 5.0 (v0 v1 v3 v5)) (* 6.0 v5)) 0.0) (<= (+ (* -9.0 (v2 v3 v5)) (* -8.0 v3) (* -8.0 (v4 v5)) (* -7.0 v5) (* -4.0 v1) (* 7.0 (v0 v1 v3 v5))) -4.0)))))))
(check-sat)
(get-model)
               """, 10))
    
