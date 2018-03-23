# Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
# 
# Licensed under the Apache License, Version 2.0 (the "License").
# You may not use this file except in compliance with the License.
# A copy of the License is located at
# 
#     http://www.apache.org/licenses/LICENSE-2.0
# 
# or in the "license" file accompanying this file. This file is distributed 
# on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either 
# express or implied. See the License for the specific language governing 
# permissions and limitations under the License.

from argparse import ArgumentParser
import os
import sys
from typing import Optional, Tuple

from frontend.program import Program
from frontend.dafny import DafnyRuntime
from frontend.rosette import RosetteRuntime


def prove(prog: str, keep=False, path: Optional[str]=None, backend_cls=DafnyRuntime) -> Tuple[bool, str]:
    p = Program(prog)

    backend = backend_cls(p)
    backend.collapse_top_level_exprs = False
    backend.output_path = os.path.dirname(os.path.realpath(__file__)) if keep else None
    if path is not None:
        backend.add_path(path)

    backend.compile(False)

    success, out, fname = backend.run(verbose=True)

    return success, fname


def main():
    ap = ArgumentParser()
    ap.add_argument("program", help="either (a) a path to a UC file, (b) a verbatim UC program, or (c) - to read from stdin")
    ap.add_argument("-k", "--keep-file", help="keep the dafny output file", action="store_true")
    ap.add_argument("-v", "--verbose", help="print backend output", action="store_true")
    ap.add_argument("-b", "--backend", choices=["dafny", "rosette"], help="logical backend to use", default="dafny")
    ap.add_argument("--path", help="additional path to search for logical backend binaries (racket/dafny)")
    args = ap.parse_args()

    runtime = RosetteRuntime if args.backend == "rosette" else DafnyRuntime

    if args.program == "-":
        sbl = sys.stdin.read()
        print("---")
    elif os.path.exists(args.program):
        with open(args.program) as f:
            sbl = f.read()
    else:
        sbl = args.program
    
    succ, fname = prove(sbl, keep=args.keep_file, path=args.path, backend_cls=runtime)

    if succ:
        print("Success!")
    else:
        print("FAILED!")
    
    if args.keep_file:
        print("  Script: " + fname)
    
    if args.verbose:
        with open(fname) as f:
            print("")
            print("Script:")
            print(f.read())
    
    sys.exit(0 if succ else 1)


if __name__ == "__main__":
    main()