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

from collections import defaultdict
from typing import List, Tuple

from .proof import Proof, Invariant

class Emitter(object):
    def emit_proof(self, prf: Proof) -> None:
        mro = type(prf).mro()
        for cls in mro:
            meth = getattr(self, 'emit_' + cls.__name__, None)
            if meth is not None:
                return meth(prf)
        raise NotImplementedError("no matching emitter for {}".format(prf))
    
    def emit_invariants(self, invs: List[Invariant]) -> List[str]:
        return [self.emit_invariant(inv) for inv in invs]

    def emit_invariant(self, inv: Invariant) -> str:
        mro = type(inv).mro()
        for cls in mro:
            meth = getattr(self, 'emit_' + cls.__name__, None)
            if meth is not None:
                return meth(inv)
        raise NotImplementedError("no matching emitter for {}".format(inv))

class LineEmitter(object):
    def __init__(self):
        self.lines = []
    def emit(self, *args):
        for line in args:
            self.lines.append(line)
    def emitComment(self, txt):
        self.lines.append("/*")
        self.lines.append(" * " + txt)
        self.lines.append("*/")
    def getLines(self):
        return self.lines

class IDGen(object):
    def __init__(self):
        self.idents = defaultdict(lambda: 0)
    def fresh(self, prefix="x"):
        i = self.idents[prefix]
        self.idents[prefix] += 1
        return prefix + str(i)
