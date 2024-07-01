import os
from argparse import ArgumentParser
from parser.formula_parser import parse_file

from tqdm import tqdm

from converter import convert
from PolyHorn.src.PolyHorn import execute_smt2
from util import set_timeout
from z3solver import SAT


class Experiment:

    def __init__(self, args):
        self.file = args.file
        self.folder = args.folder
        self.output = args.output
        self.polyhorn_config = args.config
        self.degree = args.degree
        self.convert_only = args.convert_only
        self.show_model = args.show_model
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
        models = {}

        files = [file for file in os.listdir(self.folder) if file.endswith('.m')]
        for file in (pbar := tqdm(files)):
            pbar.set_description(f'Processing {file}...')
            result = self.__main(os.path.join(self.folder, file))
            
            total += 1
            if result is not None:
                terminated += 1
                is_sat, model, ground = result
                models[file] = model
                if is_sat == ground:
                    success += 1
                if is_sat:
                    sat += 1
                else:
                    unsat += 1
            else:
                dnf.append(file)
        print('Results:')
        print('-------')
        print(f'\tTotal: {total}')
        print(f'\tTerminated: {terminated}')
        print(f'\tSuccess: {success}')
        print(f'\tSAT: {sat}')
        print(f'\tUNSAT: {unsat}')
        print(f'\tDid not terminate: {dnf}')
        if self.show_model:
            print('Models:')
            for file, model in models.items():
                print(f'{file}: {model}')

    def __run_file(self):
        result = self.__main(self.file)
        if result is None:
            print('The formula could not be solved.')
        else:
            is_sat, model, ground = result
            print(f'The formula is {"SAT" if is_sat else "UNSAT"}')
            print(f'The ground truth is {"SAT" if ground else "UNSAT"}')
            if self.show_model:
                print('Model:')
                print(model)

    def __main(self, file: str):
        quantified_formula = parse_file(file)
        converted_formula = convert(quantified_formula, degree=self.degree, output=self.output)
        
        if not self.convert_only:
            try:
                ground = set_timeout(SAT, self.timeout, quantified_formula)
            except TimeoutError:
                print(f'The ground truth could not be determined for {file}.')
                ground = None
            try:
                is_sat, model = set_timeout(execute_smt2, self.timeout, self.polyhorn_config, converted_formula)
                return is_sat, model, ground
            except TimeoutError:
                pass
        return None

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
    parser.add_argument('--show-model', action='store_true',
                        help='Show the model returned by the SMT solver.')
    parser.add_argument('--timeout', type=int, default=15,
                        help='The timeout for the SMT solver. Default is 15s.')
    args = parser.parse_args()

    experiment = Experiment(args)
    experiment.run()
