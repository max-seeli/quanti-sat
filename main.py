from argparse import ArgumentParser
import signal

from parser.formula_parser import parse_file
from converter import convert
from PolyHorn.src.PolyHorn import execute_smt2


if __name__ == '__main__':
    
    parser = ArgumentParser()
    parser.add_argument('--file', type=str, required=True, 
                        help='The file containing the formula to be converted.')
    parser.add_argument('--output', type=str, 
                        help='The file to save the SMT2 formula.')
    parser.add_argument('--config', type=str, default='polyhorn_config.json.example',
                        help='The configuration file for PolyHorn.')
    parser.add_argument('--convert-only', action='store_true',
                        help='Only convert the formula to SMT2.')
    parser.add_argument('--timeout', type=int, default=15,
                        help='The timeout for the SMT solver. Default is 15s.')
    args = parser.parse_args()
    
    quantified_formula = parse_file(args.file)
    converted_formula = convert(quantified_formula, output=args.output)
    
    if not args.convert_only:
        def timeout_handler(signum, frame):
            raise TimeoutError('The SMT solver timed out.')

        signal.signal(signal.SIGALRM, timeout_handler)
        signal.alarm(args.timeout)

        try:
            print('Executing the SMT solver...')
            execute_smt2(args.config, converted_formula)
        finally:
            signal.alarm(0)



