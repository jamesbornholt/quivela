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

from typing import Optional, List, Tuple

from .ast import *
from .analysis import GatherObjectInfo

# A Proof obligation
class Proof(object):
    def __init__(self) -> None:
        pass

# An indistinguishability proof has an LHS and an RHS executed in some context
class IndistinguishabilityProof(Proof):
    def __init__(self, lhs: AST, rhs: AST, context: AST) -> None:
        self.lhs = lhs
        self.rhs = rhs
        self.context = context


# an assertion about program state
class AssertionProof(Proof):
    def __init__(self, program: AST, condition: AST) -> None:
        self.program = program
        self.condition = condition

# prove the LHS and RHS equivalent
class EquivalenceProof(IndistinguishabilityProof):
    def __init__(self, lhs: AST, rhs: AST, context: AST, inv: Optional[AST], verb: str) -> None:
        super().__init__(lhs, rhs, context)
        self.invs = self._compute_invariant(inv)
        self.verbatim = verb
    def _compute_invariant(self, inv: Optional[AST]) -> List['Invariant']:
        if isinstance(inv, CallNode):
            if inv.name == "Equal" and len(inv.args) == 2:
                return [EqualInvariant(inv.args[0], inv.args[1])]
            elif inv.name == "&" and len(inv.args) == 2:
                collapsed = self._collapse_conjuncts(inv)
                return [i for c in collapsed for i in self._compute_invariant(c)]
            elif inv.name == "Default" and len(inv.args) == 0:
                return self._compute_default_invariant(self.context, self.lhs, self.rhs)
            elif inv.name == "Valid" and len(inv.args) == 2 and isinstance(inv.args[0], VarNode) and (inv.args[0].name == "_lhs" or inv.args[0].name == "_rhs"):
                return [ValidInvariant(inv.args[1], inv.args[0])]
            elif inv.name == "Ref" and len(inv.args) == 2 and isinstance(inv.args[0], VarNode) and (inv.args[0].name == "_lhs" or inv.args[0].name == "_rhs"):
                return [RefInvariant(inv.args[1], inv.args[0])]
            elif inv.name == "Int" and len(inv.args) == 2 and isinstance(inv.args[0], VarNode) and (inv.args[0].name == "_lhs" or inv.args[0].name == "_rhs"):
                return [IntInvariant(inv.args[1], inv.args[0])]
        elif isinstance(inv, VarNode):
            if inv.name == "true":
                return [TrueInvariant()]
            elif inv.name == "false":
                return [FalseInvariant()]
        elif isinstance(inv, MethodNode):
            if inv.name == "invariant":
                return [UniversalInvariant(inv.args, inv.body)]
        if inv is not None:
            print("Unknown invariant: {}".format(inv))
        return self._compute_default_invariant(self.context, self.lhs, self.rhs)
    def _compute_default_invariant(self, ctx: AST, lhs: AST, rhs: AST) -> List['Invariant']:
        v = GatherObjectInfo()
        v.visit(ctx)
        v.visit(lhs)
        v.visit(rhs)
        fields = sorted(set(v.get_fields(lhs)) & set(v.get_fields(rhs)))
        lhs_call = lambda name: CompoundVarNode(VarNode("_lhs"), name, ConstNil)
        rhs_call = lambda name: CompoundVarNode(VarNode("_rhs"), name, ConstNil)
        return [EqualInvariant(lhs_call(n), rhs_call(n)) for n in fields]
    def _collapse_conjuncts(self, inv: AST) -> List[AST]:
        if isinstance(inv, CallNode) and inv.name == "&" and len(inv.args) == 2:
            return self._collapse_conjuncts(inv.args[0]) + self._collapse_conjuncts(inv.args[1])
        else:
            return [inv]

class AdmitProof(IndistinguishabilityProof):
    def __init__(self, lhs: AST, rhs: AST, context: AST) -> None:
        super().__init__(lhs, rhs, context)

class RewriteProof(IndistinguishabilityProof):
    def __init__(self, lhs: AST, rhs: AST, context: AST, e1: AST, e2: AST, assumptions: List[Tuple[AST, AST]]) -> None:
        super().__init__(lhs, rhs, context)
        self.e1 = e1
        self.e2 = e2
        self.assumptions = assumptions

class RunProof(Proof):
    def __init__(self, terms: List[AST], initctx: Optional[Tuple[str, str]], expect: Optional[str]) -> None:
        self.terms = terms
        self.initctx = initctx
        self.expect = expect



class Invariant(object):
    def __init__(self) -> None:
        pass

class DefaultInvariant(Invariant):
    def __init__(self, ctx: AST, lhs: AST, rhs: AST) -> None:
        self.ctx = ctx
        self.lhs = lhs
        self.rhs = rhs

class TrueInvariant(Invariant):
    def __init__(self) -> None:
        pass

class FalseInvariant(Invariant):
    def __init__(self) -> None:
        pass

class EqualInvariant(Invariant):
    def __init__(self, lhs: AST, rhs: AST) -> None:
        self.lhs = lhs
        self.rhs = rhs

class ValidInvariant(Invariant):
    def __init__(self, expr: AST, side: VarNode) -> None:
        self.expr = expr
        self.side = side

class RefInvariant(Invariant):
    def __init__(self, expr: AST, side: VarNode) -> None:
        self.expr = expr
        self.side = side

class IntInvariant(Invariant):
    def __init__(self, expr: AST, side: VarNode) -> None:
        self.expr = expr
        self.side = side

class UniversalInvariant(Invariant):
    def __init__(self, args: List[VarNode], body: AST) -> None:
        self.args = args
        self.body = body