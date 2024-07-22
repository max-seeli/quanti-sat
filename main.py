import os
from argparse import ArgumentParser
from parser.formula_parser import parse_file
from warnings import warn
from enum import Enum
import time

from tqdm import tqdm

from util import set_timeout
from solver import QuantiSAT, Skolem
from PolyHorn.src.PositiveModel import Result as PolyHornResult


class Result(Enum):
    CORRECT = 1
    INCORRECT = 2
    CONVERSION_TIMEOUT = 3
    SOLVER_TIMEOUT = 4
    PARSING_ERROR = 5
    BUG = 6
    BUG2 = 7

class Verbosity(Enum):
    RESULT_ONLY = 1
    RESULT_FORMULA = 2
    RESULT_FORMULA_MODEL = 3

    def __str__(self):
        return self.name
    
class SolverType(Enum):
    QUANTISAT = QuantiSAT
    SKOLEM = Skolem

    def __str__(self):
        return self.name


class Experiment:

    def __init__(self, solver_type, args):
        self.solver_type = solver_type
        self.file = args.file
        self.folder = args.folder
        self.convert_only = args.convert_only
        self.verbose = args.verbose
        self.timeout = args.timeout
        self.args = args

    def run(self):
        if (self.folder is None) == (self.file is None):
            raise ValueError('You must provide either a file or a folder.')
        
        if self.folder:
            self.__run_folder()
        else:
            self.__run_file()

    def __run_folder(self):
        total, terminated, success, sat, unsat = 0, 0, 0, 0, 0
        dnf = []
        successful = []
        unsuccesful = []
        models = {}

        
        files = []


        # Get list of all files in the folder (or subfolders) with their absolute path.
        for root, _, file_names in os.walk(self.folder):
            for file_name in file_names:
                if file_name.endswith('.m') or file_name.endswith('.smt2'):
                    files.append(os.path.join(root, file_name))

        for file in (pbar := tqdm(files)):
            pbar.set_description(f'Processing {file}, Total: {success}/{total}')
            result = self.__main(file)
            
            total += 1
            if result is not None:
                terminated += 1
                is_sat, model = result
                models[file] = model
                if is_sat:
                    success += 1
                    successful.append(file)
                else:
                    unsuccesful.append(file)
                if is_sat:
                    sat += 1
                else:
                    unsat += 1
            else:
                dnf.append(file)
        print('Results:')
        print('-------')
        print(f'Total: {total}')
        print(f'Terminated: {terminated}')
        print(f'Success: {success}')
        print(f'SAT: {sat}')
        print(f'UNSAT: {unsat}')
        print(f'Did not terminate: {dnf}')
        print(f'Unsuccesful: {unsuccesful}')
        print(f'Successful: {successful}')
        if self.verbose.value >= Verbosity.RESULT_FORMULA_MODEL.value:
            print('Models:')
            for file, model in models.items():
                print(f'{file}: {model}')

    def __run_file(self):
        result = self.__main(self.file)
        print('Result:')
        print(self.__get_result_message())
        if result is not None:
            is_sat, model = result
            
            if self.verbose.value >= Verbosity.RESULT_FORMULA_MODEL.value:
                print('Model:')
                for var, value in model.items():
                    print(f"{var}: {value}")
        
        print('CSV:')
        print(f'{os.path.basename(self.file)},{self.current_result.name},{self.current_conversion_time},{self.current_solving_time},{self.num_forall_vars},{self.num_exists_vars},{self.num_switches}')

    def __main(self, file: str):
        self.current_result = None
        self.current_conversion_time = None
        self.current_solving_time = None
        self.num_forall_vars, self.num_exists_vars, self.num_switches = None, None, None

        quantified_formula = parse_file(file)
        if quantified_formula is None:
            self.current_result = Result.PARSING_ERROR
            warn("Parsing error")
            return None
        
        self.num_forall_vars, self.num_exists_vars = quantified_formula.count_quantified_vars()
        self.num_switches = quantified_formula.count_quantifier_depth()

        if self.verbose.value >= Verbosity.RESULT_FORMULA.value:
            print('Quantified formula:')
            print(quantified_formula)

        qf = self.solver_type(quantified_formula, self.args)
        nqf = self.solver_type(quantified_formula.negate(), self.args)

        try:
            qf_time = time.time()
            qf_conv = set_timeout(qf.convert, self.timeout)
            qf_time = time.time() - qf_time

            nqf_time = time.time()
            nqf_conv = set_timeout(nqf.convert, self.timeout)
            nqf_time = time.time() - nqf_time

            self.current_conversion_time = (qf_time + nqf_time) / 2
        except TimeoutError:
            self.current_result = Result.CONVERSION_TIMEOUT
            return None
        
        if self.verbose.value >= Verbosity.RESULT_FORMULA.value:
            print('Converted formula:')
            print(qf_conv)

        if not self.convert_only:
            try:
                qf_time = time.time()
                qf_result = set_timeout(qf.solve, self.timeout)
                if qf_result is None:
                    raise TimeoutError()
                is_sat, model = qf_result
                qf_time = time.time() - qf_time

                nqf_time = time.time()
                nqf_result = set_timeout(nqf.solve, self.timeout)
                if nqf_result is None:
                    raise TimeoutError()
                is_sat_neg, model_neg = nqf_result
                nqf_time = time.time() - nqf_time

                self.current_solving_time = (qf_time + nqf_time) / 2

                self.current_result = self.__evaluate_correctness(is_sat, is_sat_neg)
                if self.current_result == Result.CORRECT:
                    return True, model if is_sat else model_neg
                else:
                    return False, None
                
            except TimeoutError:
                self.current_result = Result.SOLVER_TIMEOUT
                pass
        return None
    

    def __evaluate_correctness(self, is_sat, is_sat_neg):
        if isinstance(is_sat, PolyHornResult) and isinstance(is_sat_neg, PolyHornResult):
            if is_sat_neg == PolyHornResult.SAT and is_sat == PolyHornResult.SAT:
                return Result.BUG
            elif (is_sat_neg == PolyHornResult.SAT and is_sat == PolyHornResult.UNSAT) \
                or (is_sat_neg == PolyHornResult.UNSAT and is_sat == PolyHornResult.SAT):
                return Result.CORRECT
            elif is_sat_neg == PolyHornResult.UNSAT and is_sat == PolyHornResult.UNSAT:
                return Result.INCORRECT
            else:
                return Result.BUG2
        else:
            if is_sat_neg and is_sat:
                return Result.BUG
            elif (is_sat_neg and not is_sat) or (not is_sat_neg and is_sat):
                return Result.CORRECT
            elif not is_sat_neg and not is_sat:
                return Result.INCORRECT
            else:
                return Result.BUG2

    
    def __get_result_message(self):
        match self.current_result:
            case Result.CORRECT:
                return 'The formula was solved CORRECTLY.'
            case Result.INCORRECT:
                return 'The formula was solved INCORRECTLY.'
            case Result.CONVERSION_TIMEOUT:
                return 'The formula could not be converted due to timeout.'
            case Result.SOLVER_TIMEOUT:
                return 'The formula could not be solved due to timeout.'
            case Result.PARSING_ERROR:
                return 'The formula could not be parsed.'
            case Result.BUG:
                return 'There is a BUG in the software.'
            case Result.BUG2:
                return 'There is a BUG2 in the software.'
            case _:
                raise ValueError('The experiment needs to be run before getting the result message.')

if __name__ == '__main__':
    
    parser = ArgumentParser()
    parser.add_argument('--file', type=str, 
                        help='The file containing the formula to be converted.')
    parser.add_argument('--folder', type=str,
                        help='The folder containing the formulas to be converted.')
    parser.add_argument('--output', type=str, 
                        help='The file to save the SMT2 formula.')
    parser.add_argument('--config', type=str, default='polyhorn_config.json.example',
                        help='The configuration file for PolyHorn.')
    parser.add_argument('--degree', type=int, default=1,
                        help='The degree of the templates to be used.')
    parser.add_argument('--use-template', action='store_true',
                        help='Use the template for the Skolem function. (Only used for Skolem)')
    parser.add_argument('--convert-only', action='store_true',
                        help='Only convert the formula to SMT2.')
    parser.add_argument('--solver', type=lambda v: SolverType[v], default=SolverType.QUANTISAT, choices=list(SolverType),
                        help='The solver to be used.')
    parser.add_argument('--verbose', type=lambda v: Verbosity[v], default=Verbosity.RESULT_ONLY, choices=list(Verbosity),
                        help='The verbosity level of the output.')
    parser.add_argument('--timeout', type=int, default=15,
                        help='The timeout for the SMT solver. Default is 15s.')
    args = parser.parse_args()

    experiment = Experiment(args.solver.value, args)
    experiment.run()
