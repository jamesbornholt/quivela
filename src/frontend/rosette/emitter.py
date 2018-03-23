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

import os
from typing import Any, List, Tuple

from ..emitter import *
from ..proof import *


ROSETTE_INCLUDES = ["eval.rkt", "indistinguishable.rkt", "print.rkt"]
ROSETTE_BACKEND_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "../../backend/rosette"))


class RosetteEmitter(Emitter):
    def __init__(self, includes: List[str]=[]) -> None:
        self.includes = [os.path.join(ROSETTE_BACKEND_ROOT, i) for i in ROSETTE_INCLUDES]
        self.bodies = []  # type: List[str]
        self.to_run = []  # type: List[str]
        self.id = IDGen()
        self.current_name = None  # type: Optional[str]
        self.current_args = None  # type: Optional[List[str]]
        self.current_body = LineEmitter()
    
    def start_method(self, name: str, args: List[str]=[], verbatim=False) -> str:
        assert self.current_name is None
        self.current_name = self.id.fresh(name) if not verbatim else name
        self.current_args = args
        self.current_body = LineEmitter()
        return self.current_name

    def start_function(self, name: str, args: List[str]=[]) -> str:
        assert self.current_name is None
        self.current_name = self.id.fresh(name)
        self.current_args = args
        self.current_body = LineEmitter()
        return self.current_name
    
    def end(self, run=False) -> str:
        assert self.current_name is not None
        name = self.current_name
        body = "\n".join("  {}".format(l) for l in self.current_body.getLines())
        args = " ".join(n for n in self.current_args)
        if args != "":
            args = " " + args
        func = "(define ({name}{args})\n{body})".format(name=name, args=args, body=body)
        self.bodies.append(func)
        if run:
            if self.current_args == []:
                self.to_run.append(self.current_name)
            else:
                raise Exception("cannot run a method with non-empty args")
        self.current_name = None
        return name

    def emit_global(self, *lines: str) -> None:
        self.bodies.append("\n".join(lines))

    def emit(self, *lines) -> None:
        assert self.current_name is not None
        for l in lines:
            self.current_body.emit(l)


    def to_program(self) -> str:
        body = ["({})".format(n) for n in self.to_run]
        prelude = "#lang rosette\n\n" + "\n".join('(require (file "{}"))'.format(i.replace("\\", "\\\\")) for i in self.includes)
        program = "\n\n".join([prelude] + self.bodies + body)
        return program


    def emit_AssertionProof(self, prf: AssertionProof) -> None:
        prog = self.id.fresh("prog")
        ctx  = self.id.fresh("ctx")
        ret  = self.id.fresh("ret")
        cond = self.id.fresh("cond")
        self.start_method("assertion")
        self.emit(
            "(define {} {})".format(prog, prf.program.to_sexp()),
            "(match-define (cons _ {}) (Eval {} (EmptyContext) FUEL))".format(ctx, prog),
            "(define {} {})".format(cond, prf.condition.to_sexp()),
            "(match-define (cons {} _) (Eval {} {} FUEL));".format(ret, cond, ctx),
            "(check-assert (equal? {} (Int 1)))".format(ret))
        self.end(True)
    
    def emit_EquivalenceProof(self, prf: EquivalenceProof) -> None:
        invs = self.emit_invariants(prf.invs)
        ctx  = self.id.fresh("ctx")
        lhs  = self.id.fresh("lhs")
        rhs  = self.id.fresh("rhs")
        ret1 = self.id.fresh("ret")
        ret2 = self.id.fresh("ret")
        ctx1 = self.id.fresh("ctx")
        ctx2 = self.id.fresh("ctx")
        self.start_method("equivalent")
        self.emit(
            "(define {} {})".format(ctx, prf.context.to_sexp()),
            "(define {} {})".format(lhs, prf.lhs.to_sexp()),
            "(define {} {})".format(rhs, prf.rhs.to_sexp()),
            "(define invariants (list {}))".format(" ".join(i for i in invs)),
            "(check-proof (Equivalent {} {} {} invariants))".format(ctx, lhs, rhs))
        self.end(True)
    
    def emit_AdmitProof(self, prf: AdmitProof) -> None:
        self.start_method("admitted")
        lhs = self.id.fresh("lhs")
        rhs = self.id.fresh("rhs")
        self.emit(
            "(define {} {})".format(lhs, prf.lhs.to_sexp()),
            "(define {} {})".format(rhs, prf.rhs.to_sexp()),
            "; this goal is admitted",
            "(check-proof (AdmitProof {} {}))".format(lhs, rhs))
        self.end(True)
    
    def emit_RewriteProof(self, prf: RewriteProof) -> None:
        self.start_method("validrewrite")
        ctx = self.id.fresh("ctx")
        lhs = self.id.fresh("lhs")
        rhs = self.id.fresh("rhs")
        assumptions = self.id.fresh("assumptions")
        all_assumptions = prf.assumptions + [(r,l) for l,r in prf.assumptions]
        assumptions_list = "(list" + " ".join(["(cons {} {})".format(l.to_sexp(), r.to_sexp()) for l, r in all_assumptions]) + ")"
        self.emit(
            "(define {} {})".format(ctx, prf.context.to_sexp()),
            "(define {} {})".format(lhs, prf.lhs.to_sexp()),
            "(define {} {})".format(rhs, prf.rhs.to_sexp()),
            "(define {} {})".format(assumptions, assumptions_list),
            "(check-proof (ValidRewrite {} {} {} {} {} {}))".format(lhs, rhs, ctx, prf.e1.to_sexp(), prf.e2.to_sexp(), assumptions))
        self.end(True)
    
    def emit_RunProof(self, prf: RunProof) -> None:
        initial_context = "(EmptyContext)"
        if prf.initctx is not None:
            k, v = prf.initctx
            initial_context = "(Context-with-objs (EmptyContext) (list (cons 0 (Object (list (cons '{} (Int {})))))))".format(k, v)
        
        self.start_method("run")

        initctx = self.id.fresh("initctx")
        self.emit("(define {} {})".format(initctx, initial_context))

        ctx = initctx
        ret = None
        for t in prf.terms:
            expr = self.id.fresh("expr")
            ret = self.id.fresh("ret")
            newctx = self.id.fresh("ctx")
            self.emit(
                "(define {} {})".format(expr, t.to_sexp()),
                "(match-define (cons {} {}) (Eval {} {} FUEL))".format(ret, newctx, expr, ctx),
                '(print-expr {}) (display " ==> ") (print-value {}) (display "\\n")'.format(expr, ret))
            ctx = newctx
        
        if prf.expect is not None and prf.expect != "None":
            try:
                x = int(prf.expect)
                self.emit("(check-assert (equal? {} (Int {})))".format(ret, x))
            except ValueError:
                self.emit("(check-assert ({}? {}))".format(prf.expect, ret))

        self.end(True)
    

    def emit_EquivalenceInvariant(self, name: str, args: List[str], body: List[str]) -> str:
        name = self.id.fresh(name)
        bodytxt = "\n".join("    {}".format(l) for l in body)
        lbda = "(lambda ({})\n{})".format(" ".join(args), bodytxt)
        defn = "  (EquivalenceInvariant {})".format(lbda)
        self.emit_global(
            "(define {}\n{})".format(name, defn)
        )
        return name


    def emit_DefaultInvariant(self, inv: DefaultInvariant) -> str:
        return 'DefaultInvariant'
    
    def emit_TrueInvariant(self, inv: TrueInvariant) -> str:
        return self.emit_EquivalenceInvariant("true_invariant", ["ctx1", "ctx2", "addr1", "addr2"], ["#t"])
    
    def emit_FalseInvariant(self, inv: FalseInvariant) -> str:
        return self.emit_EquivalenceInvariant("false_invariant", ["ctx1", "ctx2", "addr1", "addr2"], ["#f"])
    
    def emit_EqualInvariant(self, inv: EqualInvariant) -> str:
        body = [
            "(define (extend-with tag val ctx) (Context-with-scope ctx (assoc-set tag val (Context-scope ctx))))",
            "(define ctx1* (extend-with '_lhs (Ref addr1) ctx1))",
            "(define ctx2* (extend-with '_rhs (Ref addr2) ctx2))",
            "(match-define (cons lhs* _) (Eval {} ctx1*))".format(inv.lhs.to_sexp()),
            "(match-define (cons rhs* _) (Eval {} ctx2*))".format(inv.rhs.to_sexp()),
            "(equal? lhs* rhs*)"
        ]
        return self.emit_EquivalenceInvariant("equal_invariant", ["ctx1", "ctx2", "addr1", "addr2"], body)
    
    def emit_ValidInvariant(self, inv: ValidInvariant) -> str:
        ctx = "ctx1" if inv.side.name == "_lhs" else "ctx2"
        addr = "addr1" if inv.side.name == "_lhs" else "addr2"
        body = [
            """(define ctx (Context-with-ths {} {}))""".format(ctx, addr),
            """(match-define (cons ret _) (Eval {} ctx))""".format(inv.expr.to_sexp()),
            """(not (Error? ret))"""
        ]
        return self.emit_EquivalenceInvariant("valid_invariant", ["ctx1", "ctx2", "addr1", "addr2"], body)
    
    def emit_RefInvariant(self, inv: RefInvariant) -> str:
        ctx = "ctx1" if inv.side.name == "_lhs" else "ctx2"
        addr = "addr1" if inv.side.name == "_lhs" else "addr2"
        body = [
            """(define ctx (Context-with-ths {} {}))""".format(ctx, addr),
            """(match-define (cons ret _) (Eval {} ctx))""".format(inv.expr.to_sexp()),
            """(Ref? ret)"""
        ]
        return self.emit_EquivalenceInvariant("ref_invariant", ["ctx1", "ctx2", "addr1", "addr2"], body)
    
    def emit_IntInvariant(self, inv: IntInvariant) -> str:
        ctx = "ctx1" if inv.side.name == "_lhs" else "ctx2"
        addr = "addr1" if inv.side.name == "_lhs" else "addr2"
        body = [
            """(define ctx (Context-with-ths {} {}))""".format(ctx, addr),
            """(match-define (cons ret _) (Eval {} ctx))""".format(inv.expr.to_sexp()),
            """(Int? ret)"""
        ]
        return self.emit_EquivalenceInvariant("int_invariant", ["ctx1", "ctx2", "addr1", "addr2"], body)
    
    def emit_UniversalInvariant(self, inv: UniversalInvariant) -> str:
        # forall args. body != error
        args  = self.id.fresh("args")
        scope = self.id.fresh("scope")
        self.emit_global(
            "(define {} (list {}))".format(args, " ".join(a.to_sexp() for a in inv.args)),
            "(define {} (for/list ([v {}]) (cons (EVar-name v) (HavocArg v))))".format(scope, args)
        )
        body = [
            """(define body {})""".format(inv.body.to_sexp()),
            """(define qvs (symbolics {}))""".format(scope),
            """(match-define (cons retL _) (Call_With_Scope body ctx1 {} addr1 FUEL))""".format(scope),
            """(match-define (cons retR _) (Call_With_Scope body ctx2 {} addr2 FUEL))""".format(scope),
            """(forall qvs (and (not (Error? retL)) (not (Error? retR))))"""
        ]
        return self.emit_EquivalenceInvariant("invariant", ["ctx1", "ctx2", "addr1", "addr2"], body)
