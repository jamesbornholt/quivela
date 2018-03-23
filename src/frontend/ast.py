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

from typing import List, Any, Optional, Union

def list_to_dafny_list(lst):
    if len(lst) == 0:
        return "LNil"
    else:
        return "Cons({}, {})".format(lst[0], list_to_dafny_list(lst[1:]))
def var_list_to_dafny_list(lst):
    if len(lst) == 0:
        return "LNil"
    else:
        return 'Cons("{}", {})'.format(lst[0], var_list_to_dafny_list(lst[1:]))

class AST(object):
    def to_dafny(self) -> str:
        raise NotImplementedError()
    def to_sexp(self) -> str:
        raise NotImplementedError()
    def visit(self, visitor: 'ASTTransformer') -> None:
        raise NotImplementedError()

class ASTTransformer(object):
    def __init__(self) -> None:
        self.state = []  # type: List[Any]
    def _visit(self, node: AST) -> AST:
        mro = type(node).mro()
        for cls in mro:
            meth = getattr(self, 'visit_' + cls.__name__, None)
            if meth is not None:
                return meth(node)
        return node
    def visit(self, node: AST) -> AST:
        old_state = len(self.state)
        new_node = self._visit(node)
        new_node.visit(self)
        if len(self.state) > old_state:
            self.state = self.state[:old_state]
        return new_node


# surface-level nodes are not passed verbatim to Dafny; they must therefore have
# some special handling in the AST->Dafny compiler
class SurfaceAST(AST):
    pass

class Value(AST):
    pass


class TopLevelNode(SurfaceAST):
    def __init__(self, children: List[AST]) -> None:
        self.children = children
    def __str__(self) -> str:
        return "<TopLevelNode [{}]>".format(", ".join(str(c) for c in self.children))
    def visit(self, visitor):
        self.children = [visitor.visit(c) for c in self.children]
    # return a new TopLevelNode with consecutive non-proof terms collapsed into a single SeqNode
    def collapsed(self) -> 'TopLevelNode':
        if len(self.children) > 1:
            # flatten consecutive non-proof terms into a single SeqNote
            curr = None  # type: Optional[AST]
            new_children = []  # type: List[AST]
            for c in self.children[::-1]:
                if isinstance(c, SurfaceAST):
                    if curr is not None:
                        new_children.append(curr)
                        curr = None
                    new_children.append(c)
                elif curr is not None:
                    curr = SeqNode(c, curr)
                else:
                    curr = c
            if curr is not None:
                new_children.append(curr)
            return TopLevelNode(new_children[::-1])
        return self


class ProofNode(SurfaceAST):
    def __init__(self, terms: List[AST], hints: List[Optional[AST]], verbatims: List[str]) -> None:
        assert len(terms) > 1
        assert len(terms) == len(hints)
        self.terms = terms
        self.hints = hints
        self.verbatims = verbatims
    def __str__(self) -> str:
        return "<Proof {}>".format(" ~ ".join(str(x) for x in self.terms))
    def visit(self, visitor: ASTTransformer) -> None:
        self.terms = [visitor.visit(c) for c in self.terms]
        self.hints = [visitor.visit(c) if c is not None else c for c in self.hints]

class AssertNode(SurfaceAST):
    def __init__(self, cond: AST) -> None:
        self.cond = cond
    def __str__(self) -> str:
        return "<Assert {}>".format(self.cond)
    def visit(self, visitor: ASTTransformer) -> None:
        self.cond = visitor.visit(self.cond)

class AssumeNode(SurfaceAST):
    def __init__(self, proof: ProofNode) -> None:
        assert len(proof.terms) == 2
        self.proof = proof
    def __str__(self) -> str:
        return "<Assume {}>".format(self.proof)
    def visit(self, visitor: ASTTransformer) -> None:
        new_proof = visitor.visit(self.proof)
        if not isinstance(new_proof, ProofNode):
            raise Exception("AssumeNode expects proof to be ProofNode, got instead {}".format(new_proof))
        self.proof = new_proof

class IntNode(Value):
    def __init__(self, val: int) -> None:
        self.val = val
    def to_dafny(self) -> str:
        return 'Int({})'.format(self.val)
    def to_sexp(self) -> str:
        return '(Int {})'.format(self.val)
    def __str__(self) -> str:
        return "<IntNode {}>".format(self.val)
    def visit(self, visitor: ASTTransformer) -> None:
        pass

class NilNode(Value):
    def __init__(self) -> None:
        pass
    def to_dafny(self) -> str:
        return 'Nil()'
    def to_sexp(self) -> str:
        return '(Nil)'
    def __str__(self) -> str:
        return "<NilNode>"
    def visit(self, visitor: ASTTransformer) -> None:
        pass

class VarNode(AST):
    def __init__(self, name: str, typ: Any=None) -> None:
        self.name = name
        self.type = typ
    def to_dafny(self) -> str:
        return 'EVar("{}")'.format(self.name)
    def to_sexp(self) -> str:
        if self.type is None:
            return "(EVar '{})".format(self.name)
        else:
            return "(EVar '{} {})".format(self.name, self._type_to_sexp(self.type))
    def _type_to_sexp(self, typ: Any) -> str:
        if isinstance(typ, tuple):
            return "(list {})".format(" ".join(self._type_to_sexp(t) for t in typ))
        else:
            return "'value"
    def __str__(self) -> str:
        return "<VarNode '{}'>".format(self.name)
    def visit(self, visitor: ASTTransformer) -> None:
        pass

class ConstNode(AST):
    def __init__(self, val: Value) -> None:
        self.val = val
    def to_dafny(self) -> str:
        return 'EConst({})'.format(self.val.to_dafny())
    def to_sexp(self) -> str:
        return '(EConst {})'.format(self.val.to_sexp())
    def __str__(self) -> str:
        return "<ConstNode {}>".format(self.val)
    def visit(self, visitor: ASTTransformer) -> None:
        pass

class TupleNode(AST):
    def __init__(self, args: List[AST]) -> None:
        self.args = args
    def to_dafny(self) -> str:
        args = list_to_dafny_list([l.to_dafny() for l in self.args])
        return 'ETuple({})'.format(args)
    def to_sexp(self) -> str:
        args = " ".join(l.to_sexp() for l in self.args)
        return '(ETuple (list {}))'.format(args)
    def __str__(self) -> str:
        return "<TupleNode [{}]>".format(", ".join(str(l) for l in self.args))
    def visit(self, visitor: ASTTransformer) -> None:
        self.args = [visitor.visit(c) for c in self.args]

class SeqNode(AST):
    def __init__(self, e1: AST, e2: AST) -> None:
        self.e1 = e1
        self.e2 = e2
    def to_dafny(self) -> str:
        return 'ESeq({}, {})'.format(self.e1.to_dafny(), self.e2.to_dafny())
    def to_sexp(self) -> str:
        return '(ESeq {} {})'.format(self.e1.to_sexp(), self.e2.to_sexp())
    def __str__(self) -> str:
        return "<SeqNode {} {}>".format(self.e1, self.e2)
    def visit(self, visitor: ASTTransformer) -> None:
        self.e1 = visitor.visit(self.e1)
        self.e2 = visitor.visit(self.e2)

class CompoundVarNode(AST):
    def __init__(self, obj: AST, name: str, idx: AST) -> None:
        self.obj = obj
        self.name = name
        self.idx = idx
    def to_dafny(self) -> str:
        return 'ECVar({}, "{}", {})'.format(self.obj.to_dafny(), self.name, self.idx.to_dafny())
    def to_sexp(self) -> str:
        return "(ECVar {} '{} {})".format(self.obj.to_sexp(), self.name, self.idx.to_sexp())
    def __str__(self) -> str:
        return "<CompoundVarNode {} '{}' {}>".format(self.obj, self.name, self.idx)
    def visit(self, visitor: ASTTransformer) -> None:
        self.obj = visitor.visit(self.obj)
        self.idx = visitor.visit(self.idx)

class InitNode(AST):
    def __init__(self, name: str, val: AST, immutable: bool = False) -> None:
        self.name = name
        self.val = val
        self.immutable = immutable
    def to_dafny(self) -> str:
        return 'Init("{}", {})'.format(self.name, self.val.to_dafny())
    def to_sexp(self) -> str:
        return "(Init '{} {} {})".format(self.name, self.val.to_sexp(), "#t" if self.immutable else "#f")
    def __str__(self) -> str:
        return "<Init '{}' {} ({})>".format(self.name, self.val, self.immutable)
    def visit(self, visitor: ASTTransformer) -> None:
        self.val = visitor.visit(self.val)

class NewNode(AST):
    def __init__(self, locls: List[InitNode], body: AST) -> None:
        self.locals = locls
        self.body = body
    def to_dafny(self) -> str:
        locs = list_to_dafny_list([l.to_dafny() for l in self.locals])
        return 'ENew({}, {})'.format(locs, self.body.to_dafny())
    def to_sexp(self) -> str:
        locs = " ".join(l.to_sexp() for l in self.locals)
        return "(ENew (list {}) {})".format(locs, self.body.to_sexp())
    def __str__(self) -> str:
        return "<NewNode [{}] {}>".format(", ".join(str(l) for l in self.locals), self.body)
    def visit(self, visitor: ASTTransformer) -> None:
        new_locals = []  # type: List[InitNode]
        for c in self.locals:
            new = visitor.visit(c)
            if not isinstance(new, InitNode):
                raise Exception("NewNode expects locals to be InitNodes, got instead {}".format(new))
            new_locals.append(new)
        self.locals = new_locals
        self.body = visitor.visit(self.body)

class MethodNode(AST):
    def __init__(self, name: str, args: List[VarNode], body: AST) -> None:
        self.name = name
        self.args = args
        self.body = body
    def to_dafny(self) -> str:
        args = var_list_to_dafny_list([a.name for a in self.args])
        return 'EMethod("{}", {}, {})'.format(self.name, args, self.body.to_dafny())
    def to_sexp(self) -> str:
        args = " ".join(a.to_sexp() for a in self.args)
        return "(EMethod '{} (list {}) {})".format(self.name, args, self.body.to_sexp())
    def __str__(self) -> str:
        return "<MethodNode {} [{}] {}>".format(self.name, ", ".join("'{}'".format(a) for a in self.args), self.body)
    def visit(self, visitor: ASTTransformer) -> None:
        new_args = []  # type: List[VarNode]
        for a in self.args:
            new = visitor.visit(a)
            if not isinstance(new, VarNode):
                raise Exception("MethodNode expects args to be VarNodes, got instead {}".format(new))
            new_args.append(new)
        self.args = new_args
        self.body = visitor.visit(self.body)

class AssignNode(AST):
    def __init__(self, lhs: Union[VarNode, CompoundVarNode], rhs: AST) -> None:
        self.lhs = lhs
        self.rhs = rhs
    def to_dafny(self) -> str:
        return 'EAssign({}, {})'.format(self.lhs.to_dafny(), self.rhs.to_dafny())
    def to_sexp(self) -> str:
        return "(EAssign {} {})".format(self.lhs.to_sexp(), self.rhs.to_sexp())
    def __str__(self) -> str:
        return "<AssignNode {} {}>".format(self.lhs, self.rhs)
    def visit(self, visitor: ASTTransformer) -> None:
        new_lhs = visitor.visit(self.lhs)
        if not isinstance(new_lhs, VarNode) and not isinstance(new_lhs, CompoundVarNode):
            raise Exception("AssignNode expects LHS to be VarNode or CompoundVarNode, got instead {}".format(new_lhs))
        self.lhs = new_lhs
        self.rhs = visitor.visit(self.rhs)

class CallNode(AST):
    def __init__(self, obj: AST, name: str, args: List[AST]) -> None:
        self.obj = obj
        self.name = name
        self.args = args
    def to_dafny(self) -> str:
        args = list_to_dafny_list([a.to_dafny() for a in self.args])
        return 'ECall({}, "{}", {})'.format(self.obj.to_dafny(), self.name, args)
    def to_sexp(self) -> str:
        args = " ".join(a.to_sexp() for a in self.args)
        name = self.name.replace("|", "||")  # hack for quoting |
        return "(ECall {} '{} (list {}))".format(self.obj.to_sexp(), name, args)
    def __str__(self) -> str:
        return "<CallNode {} {} [{}]>".format(self.obj, self.name, ", ".join(str(a) for a in self.args))
    def visit(self, visitor: ASTTransformer) -> None:
        self.obj = visitor.visit(self.obj)
        self.args = [visitor.visit(c) for c in self.args]

class ITENode(AST):
    def __init__(self, cond: AST, then: AST, els: AST) -> None:
        self.cond = cond
        self.then = then
        self.els = els
    def to_dafny(self) -> str:
        return 'EITE({}, {}, {})'.format(self.cond.to_dafny(), self.then.to_dafny(), self.els.to_dafny())
    def to_sexp(self) -> str:
        return "(EITE {} {} {})".format(self.cond.to_sexp(), self.then.to_sexp(), self.els.to_sexp())
    def __str__(self) -> str:
        return "<ITENode {} {} {}>".format(self.cond, self.then, self.els)
    def visit(self, visitor: ASTTransformer) -> None:
        self.cond = visitor.visit(self.cond)
        self.then = visitor.visit(self.then)
        self.els = visitor.visit(self.els)

class NopNode(AST):
    def __init__(self) -> None:
        pass
    def to_dafny(self) -> str:
        return 'ENop()'
    def to_sexp(self) -> str:
        return "(ENop)"
    def __str__(self) -> str:
        return "<NopNode>"
    def visit(self, visitor: ASTTransformer) -> None:
        pass


ConstNil = ConstNode(NilNode())
