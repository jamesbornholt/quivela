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
from typing import Any, Dict, List, Tuple

from ..emitter import *
from ..proof import *
from ..analysis import GatherObjectInfo

from . import template


DAFNY_INCLUDES = ["Lang.dfy", "Indistinguishable.dfy", "Refl.dfy"]
DAFNY_BACKEND_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "../../backend/dafny"))


class DafnyEmitter(Emitter):
    def __init__(self, includes: List[str]=[]) -> None:
        self.includes = [os.path.join(DAFNY_BACKEND_ROOT, i) for i in DAFNY_INCLUDES]
        self.bodies = []  # type: List[str]
        self.to_run = []  # type: List[str]
        self.id = IDGen()
        self.current_type = None  # type: Optional[str]
        self.current_name = None  # type: Optional[str]
        self.current_ret  = None  # type: Optional[str]
        self.current_args = None  # type: Optional[List[Tuple[str, str]]]
        self.current_body = LineEmitter()
        self.current_annotation = LineEmitter()
    
    def start_method(self, name: str, args: List[Tuple[str, str]]=[], verbatim=False) -> str:
        assert self.current_type is None
        self.current_type = "method"
        self.current_name = self.id.fresh(name) if not verbatim else name
        self.current_ret  = None
        self.current_args = args
        self.current_body = LineEmitter()
        self.current_annotation = LineEmitter()
        return self.current_name

    def start_function(self, name: str, args: List[Tuple[str, str]], ret: str) -> str:
        assert self.current_type is None
        self.current_type = "function"
        self.current_name = self.id.fresh(name)
        self.current_args = args
        self.current_ret  = ret
        self.current_body = LineEmitter()
        self.current_annotation = LineEmitter()
        return self.current_name
    
    def start_lemma(self, name: str, args: List[Tuple[str, str]]=[], verbatim=False) -> str:
        assert self.current_type is None
        self.current_type = "lemma"
        self.current_name = self.id.fresh(name) if not verbatim else name
        self.current_ret  = None
        self.current_args = args
        self.current_body = LineEmitter()
        self.current_annotation = LineEmitter()
        return self.current_name
    
    def end(self, run=False) -> str:
        assert self.current_type is not None
        body = "\n".join("  {}".format(l) for l in self.current_body.getLines())
        annot = "\n".join("  {}".format(l) for l in self.current_annotation.getLines())
        if annot != "":
            annot += "\n"
        arglist = ", ".join("{}: {}".format(n, t) for n, t in self.current_args)
        ret = ": {}".format(self.current_ret) if self.current_ret is not None else ""
        text = "{typ} {name}({args}){ret}\n{annot}{{\n{body}\n}}".format(
            typ=self.current_type, name=self.current_name, args=arglist,
            ret=ret, annot=annot, body=body
        )
        self.bodies.append(text)
        if run:
            if self.current_args == []:
                self.to_run.append(self.current_name)
            else:
                raise Exception("can't run something at top-level with args")
        self.current_type = None
        return self.current_name


    def emit(self, *lines) -> None:
        assert self.current_type is not None
        for l in lines:
            self.current_body.emit(l)
    def emit_annotation(self, *lines) -> None:
        assert self.current_type is not None
        for l in lines:
            self.current_annotation.emit(l)
    def emit_directly(self, text: str, name: Optional[str]=None) -> None:
        self.bodies.append(text)
        if name is not None:
            self.to_run.append(name)


    def to_program(self) -> str:
        self.start_method("Main", verbatim=True)
        for name in self.to_run:
            self.emit("{}();".format(name))
        self.end()

        prelude = "\n".join('include "{}"'.format(i.replace("\\", "\\\\")) for i in self.includes)
        program = "\n\n".join([prelude] + self.bodies)
        return program


    def emit_AssertionProof(self, prf: AssertionProof) -> None:
        prog = self.id.fresh("prog")
        ctx  = self.id.fresh("ctx")
        ret  = self.id.fresh("ret")
        cond = self.id.fresh("cond")
        self.start_method("assertion")
        self.emit(
            "var {} := {};".format(prog, prf.program.to_dafny()),
            "var (_, {}) := Eval({}, EmptyContext(), FUEL);".format(ctx, prog),
            "var {} := {};".format(cond, prf.condition.to_dafny()),
            "var {} := Eval({}, {}, FUEL).0;".format(ret, cond, ctx),
            "assert {} == Int(1);".format(ret))
        self.end(True)
    
    def emit_EquivalenceProof(self, prf: EquivalenceProof) -> None:
        # first, gather the methods from the AST
        v = GatherObjectInfo()
        v.visit(prf.context)
        v.visit(prf.lhs)
        v.visit(prf.rhs)
        lhs_methods = v.get_methods(prf.lhs)
        rhs_methods = v.get_methods(prf.rhs)

        proof_name = self.id.fresh("equivalent")

        # the common stuff
        prefix = prf.context.to_dafny()
        lhs = prf.lhs.to_dafny()
        rhs = prf.rhs.to_dafny()
        invs = self.emit_invariants(prf.invs)

        # build a single invariant that conjoins all invariants together
        if len(invs) > 1:
            self.start_function("invariant", [("ctx1", "Context"), ("ctx2", "Context"), ("addr1", "Addr"), ("addr2", "Addr")], "bool")
            calls = " && ".join("{}(ctx1, ctx2, addr1, addr2)".format(i) for i in invs)
            self.emit(calls)
            inv = self.end()
        elif len(invs) == 1:
            inv = invs[0]
        else:
            inv = self.emit_TrueInvariant(TrueInvariant())

        # generate a new lemma for each method
        lemmas = []  # type: List[str]
        if lhs_methods is not None and rhs_methods is not None:
            common_methods = {}  # type: Dict[str, MethodNode]
            for n, m in lhs_methods.items():
                if n in rhs_methods and len(rhs_methods[n].args) == len(m.args):
                    common_methods[n] = m
            for name in sorted(common_methods):
                lemma_name = "{}_{}".format(proof_name, name)
                lemma_args = [(self.id.fresh("v"), "Value") for _ in common_methods[name].args]
                arg_list = ", ".join("{}: Value".format(v) for v, _ in lemma_args)
                bvs = arg_list
                if arg_list != "":
                    arg_list = ", " + arg_list
                arg_bindings = list_to_dafny_list([v for v, _ in lemma_args])
                # generate the lemma
                tmpl = template.equivalence.get("method_proof")
                text = tmpl.substitute(
                    proof=lemma_name, method=name, prefix=prefix, lhs=lhs, rhs=rhs, cons_args=arg_bindings,
                    args=arg_list, invariant=inv, body=prf.verbatim)
                self.emit_directly(text)

                # generate the lemma invocation
                use_tmpl = template.equivalence.get("lemma_use_noargs" if lemma_args == [] else "lemma_use_args")
                args = ", ".join(v for v, _ in lemma_args)
                use_text = use_tmpl.substitute(
                    proof=lemma_name, method=name, bvs=bvs, cons_args=arg_bindings, args=args, invariant=inv
                )
                lemmas.append(use_text)
        
        # generate the final proof
        body = "\n".join(lemmas)
        tmpl = template.equivalence.get("equivalence_proof")
        text = tmpl.substitute(
            proof=proof_name, prefix=prefix, lhs=lhs, rhs=rhs, invariant=inv, body=body
        )
        self.emit_directly(text, proof_name)


    def emit_AdmitProof(self, prf: AdmitProof) -> None:
        self.start_method("admitted")
        lhs_prog = SeqNode(prf.context, prf.lhs)
        rhs_prog = SeqNode(prf.context, prf.rhs)
        lhs = self.id.fresh("lhs")
        rhs = self.id.fresh("rhs")
        self.emit(
            "var {} := {};".format(lhs, lhs_prog.to_dafny()),
            "var {} := {};".format(rhs, rhs_prog.to_dafny()),
            "// this goal is admitted",
            "assert true;")
        self.end(True)

    def emit_RewriteProof(self, prf: RewriteProof) -> None:
        self.start_method("validrewrite")
        ctx = self.id.fresh("ctx")
        lhs = self.id.fresh("lhs")
        rhs = self.id.fresh("rhs")
        assumptions = self.id.fresh("assumptions")
        all_assumptions = prf.assumptions + [(r,l) for l,r in prf.assumptions]
        assumptions_list = "[" + ", ".join(["({}, {})".format(l.to_dafny(), r.to_dafny()) for l, r in all_assumptions]) + "]"
        self.emit(
            "var {} := {};".format(ctx, prf.context.to_dafny()),
            "var {} := {};".format(lhs, prf.lhs.to_dafny()),
            "var {} := {};".format(rhs, prf.rhs.to_dafny()),
            "var {} := {};".format(assumptions, assumptions_list),
            "assert ValidRewrite({}, {}, {}, {}, {}, {});".format(ctx, lhs, rhs, prf.e1.to_dafny(), prf.e2.to_dafny(), assumptions))
        self.end(True)

    def emit_RunProof(self, prf: RunProof) -> None:
        initial_context = "EmptyContext()"
        if prf.initctx is not None:
            k, v = prf.initctx
            initial_context = "EmptyContext().(objs := AssocSet(EmptyContext().objs, 0, Object(Cons(Pair(\"{}\", Int({})), LNil))))".format(k, v)
        
        self.start_method("run")

        initctx = self.id.fresh("initctx")
        self.emit("var {} := {};".format(initctx, initial_context))

        ctx = initctx
        ret = None
        for t in prf.terms:
            expr = self.id.fresh("expr")
            ret = self.id.fresh("ret")
            newctx = self.id.fresh("ctx")
            self.emit(
                "var {} := {};".format(expr, t.to_dafny()),
                "var ({}, {}) := Eval({}, {}, FUEL);".format(ret, newctx, expr, ctx),
                'Reflect_Expr({}); print " ==> "; Reflect_Value({}); print "\\n";'.format(expr, ret))
            ctx = newctx
        
        if prf.expect is not None and prf.expect != "None":
            try:
                x = int(prf.expect)
                self.emit("assert {} == Int({});".format(ret, x))
            except ValueError:
                self.emit("assert {}.{}?;".format(ret, prf.expect))

        self.end(True)


    def emit_DefaultInvariant(self, inv: DefaultInvariant) -> str:
        return 'DefaultInvariant'

    def emit_TrueInvariant(self, inv: TrueInvariant) -> str:
        self.start_function("invariant", [("ctx1", "Context"), ("ctx2", "Context"), ("addr1", "Addr"), ("addr2", "Addr")], "bool")
        self.emit("true")
        return self.end()

    def emit_FalseInvariant(self, inv: FalseInvariant) -> str:
        self.start_function("invariant", [("ctx1", "Context"), ("ctx2", "Context"), ("addr1", "Addr"), ("addr2", "Addr")], "bool")
        self.emit("false")
        return self.end()

    def emit_EqualInvariant(self, inv: EqualInvariant) -> str:
        self.start_function("invariant", [("ctx1", "Context"), ("ctx2", "Context"), ("addr1", "Addr"), ("addr2", "Addr")], "bool")
        self.emit(
            """var ctx1' := ctx1.(scope := Cons(Pair("_lhs", Ref(addr1)), ctx1.scope));""",
            """var ctx2' := ctx2.(scope := Cons(Pair("_rhs", Ref(addr2)), ctx2.scope));""",
            """var (lhs', _) := Eval({}, ctx1', FUEL);""".format(inv.lhs.to_dafny()),
            """var (rhs', _) := Eval({}, ctx2', FUEL);""".format(inv.rhs.to_dafny()),
            """lhs' == rhs'""")
        return self.end()

    def emit_ValidInvariant(self, inv: ValidInvariant) -> str:
        self.start_function("invariant", [("ctx1", "Context"), ("ctx2", "Context"), ("addr1", "Addr"), ("addr2", "Addr")], "bool")
        ctx = "ctx1" if inv.side.name == "_lhs" else "ctx2"
        addr = "addr1" if inv.side.name == "_lhs" else "addr2"
        self.emit(
            """var ctx := {}.(ths := {});""".format(ctx, addr),
            """var ret := Eval({}, ctx, FUEL).0;""".format(inv.expr.to_dafny()),
            """!ret.Error?""")
        return self.end()

    def emit_RefInvariant(self, inv: RefInvariant) -> str:
        self.start_function("invariant", [("ctx1", "Context"), ("ctx2", "Context"), ("addr1", "Addr"), ("addr2", "Addr")], "bool")
        ctx = "ctx1" if inv.side.name == "_lhs" else "ctx2"
        addr = "addr1" if inv.side.name == "_lhs" else "addr2"
        self.emit(
            """var ctx := {}.(ths := {});""".format(ctx, addr),
            """var ret := Eval({}, ctx, FUEL).0;""".format(inv.expr.to_dafny()),
            """ret.Ref?""")
        return self.end()

    def emit_IntInvariant(self, inv: IntInvariant) -> str:
        self.start_function("invariant", [("ctx1", "Context"), ("ctx2", "Context"), ("addr1", "Addr"), ("addr2", "Addr")], "bool")
        ctx = "ctx1" if inv.side.name == "_lhs" else "ctx2"
        addr = "addr1" if inv.side.name == "_lhs" else "addr2"
        self.emit(
            """var ctx := {}.(ths := {});""".format(ctx, addr),
            """var ret := Eval({}, ctx, FUEL).0;""".format(inv.expr.to_dafny()),
            """ret.Int?""")
        return self.end()
