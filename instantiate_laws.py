#!/usr/bin/python3
import glob
import os
import re
import sys
from stat import S_IREAD, S_IRGRP, S_IROTH
from typing import Union, Collection, Match, Dict, Optional, Tuple

had_errors = False


def multisubst(mappings: Collection[(Union[re.Pattern, str])], content: str) -> str:
    replacements = []
    patterns = []
    i = 0
    for pat, repl in mappings:
        if isinstance(pat, str):
            pat_str = re.escape(pat)
        else:
            pat_str = pat.pattern
        replacements.append(repl)
        patterns.append(f"(?P<GROUP_{i}>\\b(?:{pat_str})\\b)")
        i += 1

    pattern = re.compile("|".join(patterns))

    def repl_func(m: Match):
        # print(m)
        for name, text in m.groupdict().items():
            if text is None:
                continue
            if text.startswith("GROUP_"):
                continue
            idx = int(name[6:])
            # print(name, idx)
            return replacements[idx]
        assert False

    return pattern.sub(repl_func, content)

def write_to_file(file, content):
    try:
        with open(file, 'rt') as f:
            old_content = f.read()
        if content == old_content:
            print("(Nothing changed, not writing.)")
            return
        os.remove(file)
    except FileNotFoundError: pass

    with open(file, 'wt') as f:
        f.write(content)
    os.chmod(file, S_IREAD | S_IRGRP | S_IROTH)

def rewrite_laws(outputfile, substitutions):
    print(f"Rewriting Laws.thy -> {outputfile}")
    with open('Laws.thy', 'rt') as f:
        content = f.read()
    new_content = multisubst(substitutions.items(), content)

    new_content = """(*
 * This is an autogenerated file. Do not edit.
 * The original is Laws.thy. It was converted using instantiate_laws.py.
 *)

""" + new_content

    write_to_file(outputfile, new_content)


def read_instantiation_header(file: str) -> Optional[Tuple[str, Dict[str, str]]]:
    global had_errors
    with open(file, 'rt') as f:
        content = f.read()

    assert file.startswith("Axioms_")
    basename = file[len("Axioms_"):]
    assert basename.endswith(".thy")
    basename = basename[:-len(".thy")]

    m = re.compile(r"""\(\* AXIOM INSTANTIATION [^\n]*\n(.*?)\*\)""", re.DOTALL).search(content)
    if m is None:
        print(f"*** Could not find AXIOM INSTANTIATION header in {file}.")
        had_errors = True
        lines = []
    else:
        lines = m.group(1).splitlines()
    substitutions = {
        'theory Laws': f'theory Laws_{basename}',
        'Axioms': f'Axioms_{basename}'
    }
    # print(substitutions)
    for line in lines:
        if line.strip() == "":
            continue
        if re.match(r"^\s*#", line):
            continue
        m = re.match(r"^\s*(.+?)\s+\\<rightarrow>\s+(.+?)\s*$", line)
        if m is None:
            print(f"*** Invalid AXIOM INSTANTIATION line in {file}: {line}")
            had_errors = True
            continue
        key = m.group(1)
        val = m.group(2)
        if key in substitutions:
            print(f"*** Repeated AXIOM INSTANTIATION key in {file}: {line}")
            had_errors = True
        substitutions[key] = val
    # print(substitutions)
    return (f"Laws_{basename}.thy", substitutions)

def rewrite_all():
    for f in glob.glob("Axioms_*.thy"):
        lawfile, substitutions = read_instantiation_header(f)
        rewrite_laws(lawfile, substitutions)

rewrite_all()
if had_errors:
    sys.exit(1)