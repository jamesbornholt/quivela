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

from typing import List, Tuple, Optional

from .ast import *
from .proof import *
from .parser import string_to_ast
from .analysis import AnnotateImmutableLocals

class Program(object):
    def __init__(self, prog: str) -> None:
        self.ast = self.annotate_ast(string_to_ast(prog))  # type: TopLevelNode
        self.initial_context = None  # type: Optional[Tuple[str, str]]
        self.expected_return = None  # type: Optional[str]
    
    def annotate_ast(self, ast: TopLevelNode) -> TopLevelNode:
        v = AnnotateImmutableLocals()
        ret =  v.visit(ast)
        if not isinstance(ret, TopLevelNode):
            raise Exception("TopLevelNode was lost while annotating; got instead {}".format(ret))
        return ret

    def generate_evaluate_obligations(self) -> List[Proof]:
        current_program = NopNode()  # type: AST
        current_terms = []  # type: List[AST]
        proofs = []  # type: List[Proof]

        for n in self.ast.children:
            if isinstance(n, AssertNode):
                prf = AssertionProof(current_program, n.cond)
                proofs.append(prf)
            elif not isinstance(n, SurfaceAST):
                current_terms.append(n)
                if isinstance(current_program, NopNode):
                    current_program = n
                else:
                    current_program = SeqNode(current_program, n)
        
        runprf = RunProof(current_terms, self.initial_context, self.expected_return)
        proofs.append(runprf)

        return proofs

    # given an AST, generate a list of proof obligations
    # that AST requires to be discharged
    def generate_proof_obligations(self) -> List[Proof]:
        current_program = NopNode()  # type: AST
        current_assumptions = []  # type: List[Tuple[AST, AST]]
        proofs = []  # type: List[Proof]

        for n in self.ast.children:
            if isinstance(n, ProofNode):
                # generate a new proof
                for (p1, p2), hint, verb in zip(zip(n.terms, n.terms[1:]), n.hints, n.verbatims):
                    prf = self._construct_proof_obligation(current_program, p1, p2, hint, verb, current_assumptions)
                    proofs.append(prf)
            elif isinstance(n, AssertNode):
                # also generates a new proof
                prf = AssertionProof(current_program, n.cond)
                proofs.append(prf)
            elif isinstance(n, AssumeNode):
                # create a new assumption
                assert isinstance(n.proof, ProofNode)
                assert len(n.proof.terms) == 2
                current_assumptions.append((n.proof.terms[0], n.proof.terms[1]))
            elif not isinstance(n, SurfaceAST):
                # append program to current_program
                if isinstance(current_program, NopNode):
                    current_program = n
                else:
                    current_program = SeqNode(current_program, n)
        
        return proofs

    # given a program (the context so far) and LHS and RHS,
    # and the hint on how to solve the proof,
    # construct a new Proof 
    def _construct_proof_obligation(self, program: AST, lhs: AST, rhs: AST, hint: AST, verb: str, assumptions: List[Tuple[AST, AST]]) -> Proof:
        if isinstance(hint, CallNode):
            if hint.name == "Rewrite" and len(hint.args) == 2:
                return RewriteProof(lhs, rhs, program, hint.args[0], hint.args[1], assumptions)
        elif isinstance(hint, VarNode):
            if hint.name == "Admit":
                return AdmitProof(lhs, rhs, program)
        return EquivalenceProof(lhs, rhs, program, hint, verb)
