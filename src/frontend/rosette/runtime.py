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
from .emitter import RosetteEmitter


class RosetteRuntime(Runtime):
    def __init__(self, prog: Program) -> None:
        super(RosetteRuntime, self).__init__()
        self.emitter = RosetteEmitter()
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
            f = tempfile.NamedTemporaryFile(mode="w", suffix=".rkt", delete=False)
            fname = f.name
        else:
            fname = os.path.realpath("test-%s.rkt" % (hashlib.md5(tmpl.encode()).hexdigest()[:8]))
            fname = os.path.join(self.output_path, fname)
            f = open(fname, "w")
        
        f.write(tmpl)
        f.close()

        binary = self._find_executable("racket")
        stdout = None if verbose else subprocess.PIPE
        stderr = None if verbose else subprocess.PIPE
        proc = subprocess.Popen(binary + " " + fname,
                    stdout=stdout, stderr=stderr, shell=True, universal_newlines=True)
        
        out, err = proc.communicate()
        success = proc.returncode == 0

        return success, "" if verbose else (out + err), fname
