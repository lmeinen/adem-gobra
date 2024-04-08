from typing import List, Tuple
from plot import performance_plot
import subprocess

BINARY_NAME = "mmm.o"
C_FILE = "mmm.c"


def flops(n: int) -> int:
    return 2 * n**3


def run() -> List[Tuple[int, float]]:
    data = []
    for n in range(100, 1600, 100):
        print("running for n = {}...".format(n))
        cycles = float(
            subprocess.check_output(
                "./{} {}".format(BINARY_NAME, n), shell=True
            ).decode()
        )
        print("took {} cycles --> {} flops/cycle".format(cycles, flops(n) / cycles))
        data.append((n, flops(n) / cycles))
    return data


def build(*flags):
    cmd = "gcc "
    for f in flags:
        cmd = cmd + f + " "
    cmd = cmd + "-o {} {}".format(BINARY_NAME, C_FILE)
    print("building '{}'...".format(cmd))
    subprocess.call(cmd, shell=True)


def build_and_run(*flags):
    build(*flags)
    data = run()
    return " ".join(flags), data


values = {}
flags, data = build_and_run("-O0")
values[flags] = data
flags, data = build_and_run("-O3", "-fno-tree-vectorize")
values[flags] = data
flags, data = build_and_run("-O3", "-ffast-math", "-march=native")
values[flags] = data
performance_plot(values=values, title="mmm optimization flags", file_name="mmm_opt.png")
