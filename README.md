A fork of VeCoGen that generates formal ACSL specifications from C code.

## INPUT

1. C code that should be used to generate an ACSL specification
2. API KEY set in .env

## Running the tool manually

## Create a python virtual environment

python -m venv .venv
. .venv/bin/activate
pip install -r requirements.txt

### Prerequisites

- Python 3.6 or higher
- Python dependencies listed in requirements.txt (python3 -m pip install -r requirements.txt)
- Frama-c (https://frama-c.com/)
- Why3 (https://why3.lri.fr/)
- Provers in the Why3 platform, i.e. Alt-Ergo, CVC4, and Z3

### Provers

- alt-ergo 2.4.3 (https://alt-ergo.lri.fr/)
- CVC4 1.7 (https://cvc4.github.io/)
- Z3 4.8.6

# TODO: Finish this
