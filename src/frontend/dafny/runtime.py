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

import hashlib
import os
import subprocess
import sys
import tempfile
from typing import Tuple

from ..ast import *
from ..runtime import Runtime
from ..program import Program
from .emitter import DafnyEmitter


class DafnyRuntime(Runtime):
    def __init__(self, prog: Program) -> None:
        super(DafnyRuntime, self).__init__()
        self.emitter = DafnyEmitter()
        self.prog = prog

    def compile(self, evaluate=False) -> None:
        if evaluate:
            proofs = self.prog.generate_evaluate_obligations()
        else:
            proofs = self.prog.generate_proof_obligations()

        for p in proofs:
            self.emitter.emit_proof(p)

    def run(self, verbose=False) -> Tuple[bool, str, str]:
        tmpl = self.emitter.to_program()

        if self.output_path is None:
            f = tempfile.NamedTemporaryFile(mode="w", suffix=".dfy", delete=False)
            fname = f.name
        else:
            fname = os.path.realpath("test-%s.dfy" % (hashlib.md5(tmpl.encode()).hexdigest()[:8]))
            fname = os.path.join(self.output_path, fname)
            f = open(fname, "w")
        
        f.write(tmpl)
        f.close()

        binary = self._find_executable("dafny")
        stdout = None if verbose else subprocess.PIPE
        stderr = None if verbose else subprocess.PIPE
        proc = subprocess.Popen(binary + " /compile:3 /induction:1 " + fname,
                    stdout=stdout, stderr=stderr, shell=True, universal_newlines=True)

        out, err = proc.communicate()
        success = proc.returncode == 0

        if success and not verbose and "Running..." in out:
            out = out.split("Running...")[1].strip()
        
        return success, "" if verbose else (out + err), fname
