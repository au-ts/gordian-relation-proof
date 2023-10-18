"""
This is not meant to be nice to use. Talk to me (Mathieu) if you are actually
making changes to the spec and want something nicer.
"""

import sys
import subprocess
from enum import Enum
from typing_extensions import assert_never

def run(*cmd):
    try:
        p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    except FileNotFoundError as e:
        print("Couldn't find program to run, exiting", e)
        exit(1)
    p.wait()

    pretty_cmd = " ".join(cmd)

    assert p.stdout is not None
    assert p.stderr is not None

    stdout = p.stdout.read().decode("utf-8")
    stderr = p.stderr.read().decode("utf-8")

    if stderr != "":
        print(f"Got unexpected message on stderr running '{pretty_cmd}', exiting:")
        print(stderr)
        exit(2)
    if p.returncode != 0:
        print(f"non-zero return code running '{pretty_cmd}': {p.returncode}")
        exit(3)

    return stdout

content = run("z3", "--version")
if "Z3 version 4.12.1" not in content:
    print("WARNING: you're not using the same version of Z3")
    print("Proofs might not go through")

content = run("z3", "spec.smt2")
lines = content.splitlines()

class CheckerState(Enum):
    REST = 'REST'
    EXPECTING_SAT = 'EXPECTING_SAT'
    EXPECTING_UNSAT = 'EXPECTING_UNSAT'

state = CheckerState.REST

def print_err(*args, **kwargs):
    print(*args, **kwargs, file=sys.stderr)

num_proofs = 0

for line in lines:
    if state is CheckerState.REST:
        if line.startswith(';'):
            # ignore comment
            continue
        elif line.startswith("??"):
            state = CheckerState.EXPECTING_SAT
        elif line.startswith("!!"):
            state = CheckerState.EXPECTING_UNSAT
        else:
            print_err(f"Invalid line start: {line!r}")
            print_err(f"To output a comment, prefix with a ';'")
            exit(5)
    elif state is CheckerState.EXPECTING_SAT:
        if line != 'sat':
            print_err(f"Expected sat, but got {line!r}")
            exit(5)

        state = CheckerState.REST
        num_proofs += 1
    elif state is CheckerState.EXPECTING_UNSAT:
        if line != 'unsat':
            print_err(f"Expected unsat, but got {line!r}")
            exit(5)

        state = CheckerState.REST
        num_proofs += 1
    else:
        assert_never(state)

if state is not CheckerState.REST:
    print_err(f"Checker isn't in a rest state {state}")
    print_err(f"Declared proof goals wasn't discharged")
    exit(5)

print(f"All good, {num_proofs} proofs checked out :)")
