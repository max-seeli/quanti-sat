# quanti-sat
Solving the satisfiability on quantified formulas


## Quick Start
1. Install the required packages
```bash
git submodule update --init --recursive

pip install -r requirements.txt
```

2. Add formulas to the `examples/` directory

3. Add a configuration file for PolyHorn
```bash
cp polyhorn_config.json.example polyhorn_config.json
```

4. Run the solver
```bash
python3 main.py --file examples/formula_example.m --config polyhorn_config.json
```

