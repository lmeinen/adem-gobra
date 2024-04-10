"""
The program counts and reports lines of code and lines of annotation for ADEM.
Currently a line is considered to be a line of code if all of these hold:
- It is inside a '.go' file with the header // +gobra
- It is not just whitespace
- It is not a single line comment
A line of annotation is a line for which either holds:
- It is inside a '.gobra' file with the header // +gobra and is not a single line comment or blank
- It is inside a '.go' file with the header // +gobra and starts with (possibly whitespace) and,
  '// @' or '//@' OR it is within '/*@' '@*/' tags

Current limitations:
- The program does not count inlining of ghost code in lines
"""

import os
from os import path
import re

PACKAGES = ["consts", "util", "ident", "roots", "tokens", "vfy"]


def has_header(fname):
    with open(fname, "r") as fhandle:
        for line in fhandle:
            if line.startswith("package"):
                return False
            if "+gobra" in line:
                return True
    return None


def handle_go_file(fname):
    loc = 0
    loa = 0
    gobra_mode = False
    with open(fname, "r") as fhandle:
        for line in fhandle:
            if gobra_mode:
                if re.match(r"\s*@\*/", line):
                    gobra_mode = False
                elif (len(line.strip()) > 0) and not (re.match(r"\s*//.*", line)):
                    loa += 1
            else:
                if re.match(r"\s*// ?@.*", line):
                    loa += 1
                elif re.match(r"/\*@.*@\*/", line):
                    # inline ghost code is counted as both
                    loa += 1
                    loc += 1
                elif re.match(r"\s*/\*@", line):
                    gobra_mode = True
                elif (len(line.strip()) > 0) and not (re.match(r"\s*//.*", line)):
                    loc += 1
    return loc, loa


def handle_gobra_file(fname):
    loa = 0
    with open(fname, "r") as fhandle:
        for line in fhandle:
            if (len(line.strip()) > 0) and not (re.match(r"\s*//.*", line)):
                loa += 1
    return loa


loc = 0  # lines of code
loa = 0  # lines of annotation

for dirname, dirs, files in os.walk("../", topdown=True):
    # exclude dotted directories
    dirs[:] = [d for d in dirs if (not path.split(d)[-1].startswith("."))]
    tocheck = [
        path.join(dirname, f)
        for f in files
        if (f.endswith(".go") or f.endswith(".gobra"))
        and has_header(path.join(dirname, f))
    ]
    local_loc = 0
    local_loa = 0
    if len(tocheck) > 0:
        for f in tocheck:
            if f.endswith(".go"):
                new_loc, new_loa = handle_go_file(f)
            else:
                new_loc = 0
                new_loa = handle_gobra_file(f)
            local_loc += new_loc
            local_loa += new_loa
    elems = dirname.split("/")
    if elems[-2] == "pkg" and elems[-1] in PACKAGES:
        print(f"{elems[-1]} LOC: {local_loc}")
        print(f"{elems[-1]} LOA: {local_loa}")
    loc += local_loc
    loa += local_loa

print(f"Lines of Code: {loc}")
print(f"Lines of Annotation: {loa}")
