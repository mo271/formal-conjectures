#!/usr/bin/env python3
"""Fail on build warnings from this repository, but not from its dependencies.

`lake --wfail build` fails on a warning in any module, including the modules
of dependencies. Some dependencies, such as `Apery` (mo271/zeta5) and
`PrimeNumberTheoremAnd`, log many warnings that this repository cannot fix.
So CI builds the problems without `--wfail` and runs this script on the JSON
summary that `lake-build-wrapper.py` writes. The script fails when a warning
or error block belongs to one of this repository's libraries.

Usage:
  python3 lake-build-wrapper.py summary.json lake build
  python3 check_build_warnings.py summary.json
"""

import argparse
import json
import pathlib
import sys

# Module roots of the libraries in `lakefile.toml`.
OWN_ROOTS = (
    "FormalConjectures",
    "FormalConjecturesForMathlib",
    "FormalConjecturesUtil",
    "FormalConjecturesTest",
    "FormalConjecturesAnswerPostpone",
)

# The package name, which prefixes non-module targets such as `pkg:exe`.
OWN_PACKAGE = "formal_conjectures"


def is_own(block):
    """Whether a block from the summary belongs to this repository.

    A block without a target is counted as our own, so that a warning is
    never dropped only because its origin is unknown.
    """
    target = block.get("file_info", {}).get("target")
    if not target:
        return True
    if ":" in target:
        return target.split(":", 1)[0] == OWN_PACKAGE
    return target.split(".", 1)[0] in OWN_ROOTS


def own_blocks(summary):
    """The warning and error blocks of `summary` that belong to us."""
    return [block
            for kind in ("warnings", "errors")
            for block in summary.get(kind, [])
            if is_own(block)]


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("summary",
                        help="the JSON written by `lake-build-wrapper.py`")
    args = parser.parse_args(argv)

    try:
        summary = json.loads(pathlib.Path(args.summary).read_text("utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        print(f"::error::cannot read {args.summary}: {error}")
        return 2

    own = own_blocks(summary)
    ignored = summary.get("warning_count", 0) + summary.get("error_count", 0)
    ignored -= len(own)
    print(f"Ignored {ignored} warning or error block(s) from dependencies.")
    if own:
        print(f"Found {len(own)} warning or error block(s) in this repository:")
        for block in own:
            print(block.get("full_output", ""))
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
