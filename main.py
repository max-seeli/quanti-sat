import os
from argparse import ArgumentParser
from parser.formula_parser import parse_file
from warnings import warn
from enum import Enum
import time

from tqdm import tqdm

from util import Result
from solver import QuantiSAT, MultiQuantiSAT, Skolem, SolverBackend

class Verbosity(Enum):
    RESULT_ONLY = 1
    RESULT_FORMULA = 2
    RESULT_FORMULA_MODEL = 3

    def __str__(self):
        return self.name
    
class SolverType(Enum):
    QUANTISAT = QuantiSAT
    MULTIQUANTISAT = MultiQuantiSAT
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
        self.args.output = None

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

        #files = [os.path.join(root, file) for file in ['ex15_formula_197.m', 'ex08_formula_114.m', 'ex15_formula_084.m', 'ex06_formula_096.m', 'ex06_formula_039.m', 'ex17_formula_012.m', 'ex17_formula_101.m', 'ex15_formula_255.m', 'ex07_formula_278.m', 'ex12_formula_018.m', 'ex15_formula_073.m', 'ex15_formula_138.m', 'ex10_formula_132.m', 'ex16_formula_166.m', 'ex15_formula_160.m', 'ex12_formula_096.m', 'ex09_formula_041.m', 'ex08_formula_200.m', 'ex15_formula_283.m', 'ex12_formula_185.m', 'ex16_formula_272.m', 'ex12_formula_039.m', 'ex15_formula_274.m', 'ex13_formula_278.m', 'ex11_formula_067.m', 'ex06_formula_153.m', 'ex07_formula_027.m', 'ex11_formula_241.m', 'ex15_formula_141.m', 'ex16_formula_054.m', 'ex15_formula_052.m', 'ex15_formula_119.m', 'ex11_formula_219.m', 'ex13_formula_006.m', 'ex10_formula_094.m', 'ex13_formula_092.m', 'ex08_formula_156.m', 'ex13_formula_176.m', 'ex15_formula_122.m', 'ex15_formula_069.m', 'ex15_formula_031.m', 'ex15_formula_217.m']]

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
                if isinstance(model, dict):
                    print(f'{file}:')
                    for var, value in model.items():
                        print(f"{var}: {value}")

    def __run_file(self):
        result = self.__main(self.file)
        print('Result:')
        print(self.__get_result_message())
        if result is not None:
            is_sat, model = result
            
            if self.verbose.value >= Verbosity.RESULT_FORMULA_MODEL.value and is_sat:
                print('Model:')
                for var, value in model.items():
                    print(f"{var}: {value}")
        
        print('CSV:')
        if self.other_metrics is not None:
            print(f'{os.path.basename(self.file)},{self.current_result.name},{self.current_conversion_time},{self.current_solving_time},{self.num_forall_vars},{self.num_exists_vars},{self.num_switches},{",".join(str(metric) for metric in self.other_metrics)}')
        else:
            print(f'{os.path.basename(self.file)},{self.current_result.name},{self.current_conversion_time},{self.current_solving_time},{self.num_forall_vars},{self.num_exists_vars},{self.num_switches}')

    def __main(self, file: str):
        self.current_result = None
        self.current_conversion_time = None
        self.current_solving_time = None
        self.num_forall_vars, self.num_exists_vars, self.num_switches = None, None, None
        self.other_metrics = None

        constraint_system = parse_file(file)
        if constraint_system is None:
            self.current_result = Result.PARSING_ERROR
            warn("Parsing error")
            return None
        
        per_formula_quantifier_counts = [quantified_formula.count_quantified_vars() for quantified_formula in constraint_system]
        per_formula_switches = [quantified_formula.count_quantifier_depth() for quantified_formula in constraint_system]

        self.num_forall_vars = max([num_forall_vars for num_forall_vars, _ in per_formula_quantifier_counts])
        self.num_exists_vars = max([num_exists_vars for _, num_exists_vars in per_formula_quantifier_counts])
        self.num_switches = max(per_formula_switches)

        args_dict = vars(self.args)
        solver = self.solver_type(constraint_system, args_dict)
        
        try:
            conversion_time = time.time()
            solver.convert()
            self.current_conversion_time = time.time() - conversion_time

        except TimeoutError:
            self.current_result = Result.CONVERSION_TIMEOUT
            self.current_conversion_time = None
            return None
        
        if self.verbose.value >= Verbosity.RESULT_FORMULA.value:
            solver.print()

        if not self.convert_only:
            try:
                solver_time = time.time()
                self.current_result, model, other_metrics = solver.solve()
                self.current_solving_time = time.time() - solver_time
                self.other_metrics = other_metrics
                if self.current_result == Result.CORRECT:
                    return True, model
                elif self.current_result == Result.INCORRECT:
                    return False, None
                elif self.current_result == Result.SOLVER_TIMEOUT:
                    self.current_solving_time = None
                    return None
                
            except TimeoutError:
                self.current_result = Result.SOLVER_TIMEOUT
                self.current_solving_time = None
                pass
        return None
    
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
    parser.add_argument('--backend', type=lambda v: SolverBackend[v], default=SolverBackend.Z3, choices=list(SolverBackend),
                        help='The backend to be used for the Skolem solver.')
    parser.add_argument('--timeout', type=int, default=15,
                        help='The timeout for the SMT solver. Default is 15s.')
    args = parser.parse_args()

    experiment = Experiment(args.solver.value, args)
    experiment.run()
