import os
from argparse import ArgumentParser
from parser.formula_parser import parse_file
from warnings import warn
from enum import Enum
import time

from tqdm import tqdm

from converter import GenerationVariant, convert
from PolyHorn.src.main import execute_smt2
from util import set_timeout
from z3solver import SAT

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


class Experiment:

    def __init__(self, args):
        self.file = args.file
        self.folder = args.folder
        self.output = args.output
        self.polyhorn_config = args.config
        self.degree = args.degree
        self.convert_only = args.convert_only
        self.verbose = args.verbose
        self.timeout = args.timeout

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

        files = ['Ecoli-chemotaxis-node7008.smt2', 'moving-point-node2370.smt2', 'dccs-example-simple-node6247.smt2', 'vsl.proof-node1351.smt2', 'intersection-example-onelane.proof-node6566.smt2', 'dynamic_reaction_to_static_bounds.proof-node849.smt2', 'moving-point-node1721.smt2', 'dccs-example-simple-node3457.smt2', 'Ecoli-chemotaxis-node8284.smt2', 'intersection-example-onelane.proof-node9774.smt2', 'intersection-example-onelane.proof-node16095.smt2', 'Ecoli-chemotaxis-node8285.smt2', 'intersection-example-onelane.proof-node2524.smt2', 'intersection-example-onelane.proof-node11126.smt2', 'binary_driver-2007-10-09-node11384.smt2', 'intersection-example-onelane.proof-node6824.smt2', 'FTRM-entry-tang-feasible-node1796.smt2', 'rbc-controllability-characterisation-node3299.smt2', 'intersection-example-onelane.proof-node14168.smt2', 'intersection-example-onelane.proof-node3855.smt2', 'binary_driver-2007-10-09-node14896.smt2', 'ETCS-essentials-live-range2.proof-node577.smt2', 'intersection-example-onelane.proof-node8099.smt2', 'Ecoli-chemotaxis-node7007.smt2', 'rbc-controllability-characterisation-node3243.smt2', 'dynamic_reaction_to_static_bounds.proof-node839.smt2', 'intersection-example-onelane.proof-node1479.smt2', 'intersection-example-onelane.proof-node12972.smt2', 'ETCS-essentials-live2.proof-node640.smt2', 'intersection-example-onelane.proof-node13822.smt2']
        files = [os.path.join(self.folder, file) for file in files]

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
        print(f'{os.path.basename(self.file)},{self.current_result.name},{self.current_conversion_time},{self.current_solving_time}')

    def __main(self, file: str):
        self.current_result = None
        self.current_conversion_time = None
        self.current_solving_time = None

        quantified_formula = parse_file(file)
        if quantified_formula is None:
            self.current_result = Result.PARSING_ERROR
            warn("Parsing error")
            return None

        if self.verbose.value >= Verbosity.RESULT_FORMULA.value:
            print('Quantified formula:')
            print(quantified_formula)

        qf = quantified_formula
        nqf = qf.negate()

        try:
            qf_time = time.time()
            qf_conv = set_timeout(convert, self.timeout, qf, degree=self.degree, variant=GenerationVariant.FORALL_ONLY, output=self.output)
            qf_time = time.time() - qf_time

            nqf_time = time.time()
            nqf_conv = set_timeout(convert, self.timeout, nqf, degree=self.degree, variant=GenerationVariant.FORALL_ONLY, output=self.output)
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
                is_sat, model = set_timeout(execute_smt2, self.timeout, self.polyhorn_config, qf_conv)
                qf_time = time.time() - qf_time

                nqf_time = time.time()
                is_sat_neg, model_neg = set_timeout(execute_smt2, self.timeout, self.polyhorn_config, nqf_conv)
                nqf_time = time.time() - nqf_time

                self.current_solving_time = (qf_time + nqf_time) / 2

                if is_sat_neg and is_sat:
                    self.current_result = Result.BUG
                    return None
                elif (is_sat_neg and not is_sat) or (not is_sat_neg and is_sat):
                    self.current_result = Result.CORRECT
                    return is_sat, model if is_sat else model_neg
                elif not is_sat_neg and not is_sat:
                    self.current_result = Result.INCORRECT
                    return None
                else:
                    self.current_result = Result.BUG2
                    return None

            except TimeoutError:
                self.current_result = Result.SOLVER_TIMEOUT
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
    parser.add_argument('--convert-only', action='store_true',
                        help='Only convert the formula to SMT2.')
    parser.add_argument('--verbose', type=lambda v: Verbosity[v], default=Verbosity.RESULT_ONLY, choices=list(Verbosity),
                        help='The verbosity level of the output.')
    parser.add_argument('--timeout', type=int, default=15,
                        help='The timeout for the SMT solver. Default is 15s.')
    args = parser.parse_args()

    experiment = Experiment(args)
    experiment.run()
