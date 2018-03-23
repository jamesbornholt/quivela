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
from typing import Dict, Optional, Set, Union

from .ast import *


# For each object in the program, determine its methods and fields.
# An object can be either named (when a MethodNode's body is a NewNode)
# or anonymous, so that we can look up proof nodes by name (e.g., to find
# the object definition for a call Foo()).
class GatherObjectInfo(ASTTransformer):
    class ObjectInfo(object):
        def __init__(self) -> None:
            self.methods = {}  # type: Dict[str, MethodNode]
            self.fields = []  # type: List[str]
    def __init__(self) -> None:
        super().__init__()
        # We track two types of objects: named (which are methods
        # containing a NewNode body), and anonymous (which are just
        # NewNodes not contained directly in methods)
        self.ctors = defaultdict(GatherObjectInfo.ObjectInfo)  # type: Dict[str, GatherObjectInfo.ObjectInfo]
        self.anon  = defaultdict(GatherObjectInfo.ObjectInfo)  # type: Dict[AST, GatherObjectInfo.ObjectInfo]
    def get_methods(self, node: AST) -> Optional[Dict[str, MethodNode]]:
        if isinstance(node, NewNode) and node in self.anon:
            return self.anon[node].methods
        elif isinstance(node, CallNode) and node.obj is ConstNil and node.name in self.ctors:
            return self.ctors[node.name].methods
        else:
            return None
    def get_fields(self, node: AST) -> List[str]:
        if isinstance(node, NewNode) and node in self.anon:
            return self.anon[node].fields
        elif isinstance(node, CallNode) and node.obj is ConstNil and node.name in self.ctors:
            return self.ctors[node.name].fields
        else:
            return []
    def visit_NewNode(self, node: NewNode) -> AST:
        self.state.append(node)
        k = self._get_key_for_method(node)
        if isinstance(k, AST):
            self.anon[k].fields = [l.name for l in node.locals]
        elif isinstance(k, str):
            self.ctors[k].fields = [l.name for l in node.locals]
        return node
    def visit_MethodNode(self, node: MethodNode) -> AST:
        k = self._get_key_for_method(node)
        if isinstance(k, AST):
            # it's anonymous
            self.anon[k].methods[node.name] = node
        elif isinstance(k, str):
            # it's named
            self.ctors[k].methods[node.name] = node
        self.state.append(node)
        return node
    def _get_key_for_method(self, node: AST) -> Union[AST, str, bool]:
        # not contained inside a NewNode
        if not self.state or not isinstance(self.state[-1], NewNode):
            return False
        # check if our NewNode is contained inside a named method
        if len(self.state) > 1:
            if isinstance(self.state[-2], MethodNode):
                return self.state[-2].name
        # otherwise this newNode is anonymous and identified by its AST
        return self.state[-1]


# Find the set of fields mutated by each object in the program.
# We consider a field mutated if it ever appears on the left-hand side
# of an assignment.
# If we cannot precisely determine which object a mutation belongs to,
# we conservatively assume that field is mutable on *every* object.
class FindMutatedLocals(ASTTransformer):
    def __init__(self) -> None:
        super().__init__()
        # map of NewNode ASTs to the locals they mutate
        self.must_mutate = {}  # type: Dict[NewNode, Set[str]]
        # list of locals mutated on an unknown object
        # (we will conservatively assume it's *every* object)
        self.may_mutate = set()  # type: Set[str]
    def visit_NewNode(self, node: NewNode) -> AST:
        self.state.append(node)
        return node
    def visit_AssignNode(self, node: AssignNode) -> AST:
        if isinstance(node.lhs, VarNode) and self.state:
            new = self.state[-1]
            if new not in self.must_mutate:
                self.must_mutate[new] = set()
            self.must_mutate[new].add(node.lhs.name)
        elif isinstance(node.lhs, CompoundVarNode):
            self.may_mutate.add(node.lhs.name)
        return node


# Transform InitNodes to annotate their mutability.
# Uses the FindMutatedLocals visitor above to determine mutability.
class AnnotateImmutableLocals(ASTTransformer):
    def __init__(self) -> None:
        super().__init__()
        self.find = FindMutatedLocals()
    def visit(self, ast: AST) -> AST:
        self.find.visit(ast)
        return super().visit(ast)
    def visit_NewNode(self, node: NewNode) -> NewNode:
        self.state.append(node)
        return node
    def visit_InitNode(self, node: InitNode) -> InitNode:
        immutable = True
        if self.state and self.state[-1] in self.find.must_mutate:
            muts = self.find.must_mutate[self.state[-1]]
            if node.name in muts:
                immutable = False
        if node.name in self.find.may_mutate:
            immutable = False
        new = InitNode(node.name, node.val, immutable)
        return new
