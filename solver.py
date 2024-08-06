import os
from abc import ABC, abstractmethod
from typing import Dict, List, Tuple
from enum import Enum

import sympy as sp

from converter import convert
from expression import get_polynomial_expression
from PolyHorn.src.main import execute_smt2
from PolyHorn.src.PositiveModel import Result as PolyHornResult
from quantifier import Exists, ForAll, Quantifier
from util import to_smt, set_timeout, Result
from z3solver import SAT2
from cvc5solver import CVC5

class SolverBackend(Enum):
    Z3 = 1
    CVC5 = 2

class Solver(ABC):

    def __init__(self, constraint_system: List[Quantifier], args: dict):
        self.constraint_system = constraint_system
        self.disjunct_negated_system = [[formula.negate()] for formula in constraint_system]
        
        self.degree = args['degree']
        self.output = args['output']
        self.timeout = args['timeout']

        self.SAT = True
        self.UNSAT = False
        self.UNKNOWN = None

        self.smt2_pos = None
        self.smt2_negs = None
    
    @abstractmethod
    def _solve(self, smt2: str) -> Tuple[Result, Dict]:
        pass

    def convert(self):
        self.smt2_pos = set_timeout(convert, self.timeout, self.constraint_system, degree=self.degree)
        self.smt2_negs = [set_timeout(convert, self.timeout, negated_system_disjunct, degree=self.degree) for negated_system_disjunct in self.disjunct_negated_system]

        if self.output is not None:
            with open(self.output, 'w') as f:
                f.write(self.smt2_pos)
            
            neg_path = os.path.splitext(self.output)[0] + '_neg_'
            for i, neg in enumerate(self.smt2_negs):
                with open(neg_path + str(i) + '.smt2', 'w') as f:
                    f.write(neg)    

    def solve(self):
        if self.smt2_pos is None:
            raise ValueError('The formula has not been converted yet.')

        result_pos = self._solve(self.smt2_pos)

        if result_pos is not None:
            sat, model = result_pos
            if sat == self.UNKNOWN:
                print("1")
                return Result.SOLVER_TIMEOUT, {}, []
            elif sat == self.SAT:
                return Result.CORRECT, model, []
            elif sat == self.UNSAT:
                any_timeout = False
                for neg in self.smt2_negs:
                    result_neg = self._solve(neg)
                    if result_neg is not None:
                        sat_neg, model_neg = result_neg
                        if sat_neg == self.UNKNOWN:
                            any_timeout = True
                        elif sat_neg == self.UNSAT:
                            continue
                        elif sat_neg == self.SAT:
                            return Result.CORRECT, model_neg, []
                    else:
                        any_timeout = True  
                if any_timeout:
                    print("4")
                    return Result.SOLVER_TIMEOUT, {}, []
                else:
                    return Result.INCORRECT, {}, []
        else:
            print("5")
            return Result.SOLVER_TIMEOUT, {}, []

    def print(self):
        print("Converted formula:")
        print(self.smt2_pos)
        print("Converted Negated formula:")
        for i, neg in enumerate(self.smt2_negs):
            print(f"Negated formula {i}:")
            print(neg)


class MultiQuantiSAT(Solver):

    def __init__(self, constraint_system: List[Quantifier], args: dict):
        self.constraint_system = constraint_system
        
        self.configs = {'configs/farkas-z3.json': [0, 1],
                        'configs/handelman-z3.json': [0, 1, 2],
                        'configs/putinar-z3.json': [0, 1, 2]}
        
        config_args = []
        for ph_config, degrees in self.configs.items():
            for degree in degrees:
                config_args.append({'config': ph_config, 'degree': degree})
        
        self.solvers = [QuantiSAT(constraint_system, {**args, **config}) for config in config_args]

    def convert(self):
        successful = []
        for solver in self.solvers:
            try:
                solver.convert()
                successful.append(solver)
            except TimeoutError:
                continue
        
        if len(successful) == 0:
            raise TimeoutError('All conversion attempts timed out.')
        for solver in successful:
            print("Converted with", solver.polyhorn_config, solver.degree)
        self.solvers = successful


    def solve(self):
        results = []
        for solver in self.solvers:
            try:
                result, model, _ = solver.solve()
            except TimeoutError:
                results.append(Result.SOLVER_TIMEOUT)
                continue
            if result == Result.CORRECT:
                print("Solved with", solver.polyhorn_config, solver.degree)
                return Result.CORRECT, model, [solver.polyhorn_config, solver.degree]

            results.append(result)
        
        if all(result == Result.INCORRECT for result in results):
            return Result.INCORRECT, {}, [None, None]
        else:
            return Result.SOLVER_TIMEOUT, {}, [None, None]
        
    def _solve(self, smt2: str) -> Tuple[Result, Dict]:
        pass
        
    def print(self):
        self.solvers[0].print()

class QuantiSAT(Solver):

    def __init__(self, constraint_system: List[Quantifier], args: dict):
        super().__init__(constraint_system, args)

        self.SAT = PolyHornResult.SAT
        self.UNSAT = PolyHornResult.UNSAT
        self.UNKNOWN = PolyHornResult.UNKNOWN

        self.degree = args['degree']
        self.output = args['output']
        self.polyhorn_config = args['config']
        self.timeout = args['timeout']

    def _solve(self, smt2: str) -> Tuple[Result, Dict]:
        return set_timeout(execute_smt2, self.timeout, self.polyhorn_config, smt2)

class Skolem(Solver):

    def __init__(self, constraint_system: List[Quantifier], args: dict):
        super().__init__(constraint_system, args)

        self.SAT = True
        self.UNSAT = False
        self.UNKNOWN = None

        self.use_template = args['use_template']
        self.degree = args['degree']
        if not self.use_template:
            self.degree = None
        self.timeout = args['timeout']
        self.backend = args['backend']

    def _solve(self, smt2: str) -> Tuple[Result, Dict]:
        if self.backend == SolverBackend.Z3:
            return SAT2(smt2, self.timeout)
        elif self.backend == SolverBackend.CVC5:
            return CVC5(smt2, self.timeout)
        else:
            raise ValueError('Invalid backend.')

