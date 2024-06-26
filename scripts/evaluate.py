import argparse
import logging
import os
import time
import subprocess
from typing import List

logging.basicConfig()

NUM_RUNS = 10
SCRIPT = "verify.sh"
PACKAGES = ["consts", "util", "ident", "roots", "tokens", "vfy"]

parser = argparse.ArgumentParser(
    prog="ADEMGobble",
    description="Runs benchmarks to evaluate verification times for all packages in the ADEM codebase. If the verification fails, an error is reported.",
    epilog="Some arguments are communicated to the verification script as environment variables. Check the script for specifics.",
)

parser.add_argument(
    "-g",
    "--gobra",
    type=str,
    default="$HOME/repos/gobra/target/scala-2.13/gobra.jar",
    help="Path to a pre-compiled Gobra jar. See https://github.com/viperproject/gobra?tab=readme-ov-file#installation for details.",
)
parser.add_argument(
    "-t",
    "--timeout",
    default="600",
    type=int,
    help="Number of seconds before the verification should time out.",
)
parser.add_argument(
    "-s",
    "--skip",
    action="store_true",
    help="Skip verification time measurements for single packages and instead only measure total verification time. If this option is enabled, the packages option will be ignored.",
)
parser.add_argument(
    "-p",
    "--packages",
    nargs="*",
    default=PACKAGES,
    help="Packages to verify. If all packages are verified, another round of measurements will be taken for total verification time.",
    choices=PACKAGES,
)
parser.add_argument(
    "-r", "--runs", default=10, help="Number of runs to average over", type=int
)
parser.add_argument(
    "-d",
    "--debug",
    action="store_true",
    help="Debug logging level",
)


def setup(bin: str, timeout: int, ps: List[str], skip: bool) -> List[str]:
    if os.path.isfile(bin):
        os.environ["BIN"] = bin
    if timeout > 0:
        os.environ["TIMEOUT"] = f"{timeout}s"
    ls = []
    if not skip:
        for p in ps:
            ls.append(f"--includePackages {p}")
    if len(ls) == len(PACKAGES) or skip:
        # run all packages at once
        ls.append(f"")
    return ls


def bench_for_arg(arg: str) -> int:
    data = []
    for i in range(NUM_RUNS):
        tries = 0
        logging.debug(f"running for arg '{arg}' ({i + 1}/{NUM_RUNS})")
        start = time.time()
        try:
            subprocess.run(
                f"bash {os.path.dirname(__file__)}/{SCRIPT} {arg}",
                capture_output=True,
                shell=True,
                check=True,
            )
        except subprocess.CalledProcessError as e:
            logging.error(
                f"Gobra threw an exception with stdout:\n\n{e.stdout.decode('utf-8')}"
            )
            tries += 1
            if tries > 3:
                raise e
            else:
                logging.debug(f"trying again ({tries}/3)")
                i -= 1
                continue
        end = time.time()
        data.append(end - start)
    return sum(data) / len(data)


def bench(args: List[str]):
    for arg in args:
        avgtime = round(bench_for_arg(arg), 1)
        logging.info(f"{arg}: {avgtime}s")


args = parser.parse_args()

verify_args = setup(args.gobra, args.timeout, args.packages, args.skip)

if args.runs > 0:
    NUM_RUNS = args.runs
if args.debug:
    logging.getLogger().setLevel(logging.DEBUG)
else:
    logging.getLogger().setLevel(logging.INFO)

bench(verify_args)
