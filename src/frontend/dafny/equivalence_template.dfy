// Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// 
// Licensed under the Apache License, Version 2.0 (the "License").
// You may not use this file except in compliance with the License.
// A copy of the License is located at
// 
//     http://www.apache.org/licenses/LICENSE-2.0
// 
// or in the "license" file accompanying this file. This file is distributed 
// on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either 
// express or implied. See the License for the specific language governing 
// permissions and limitations under the License.

//// This file is a template used for generating equivalence proofs in the Dafny
//// backend.
//// Lines beginning with "////" are removed from the generated code.
//// Lines beginning with "///<" are also removed, and act as delimiters for
//// code generation.
//// Strings that begin with __ and end with __ are replaced during code generation.

///< START method_proof
// Equivalence proof for method `${method}`
lemma ${proof}(objs1: ObjList, objs2: ObjList${args})
  requires
    var prefix := ${prefix};
    var ctxp := Eval(prefix, EmptyContext(), FUEL).1;
    var lhs := ${lhs};
    var rhs := ${rhs};
    var (addr1, ctx1) := Eval(lhs, ctxp, FUEL);
    var (addr2, ctx2) := Eval(rhs, ctxp, FUEL);
    HavocPrecondition(ctx1, ctx2, addr1, addr2, ${invariant}, objs1, objs2)
  ensures
    var prefix := ${prefix};
    var ctxp := Eval(prefix, EmptyContext(), FUEL).1;
    var lhs := ${lhs};
    var rhs := ${rhs};
    var (addr1, ctx1) := Eval(lhs, ctxp, FUEL);
    var (addr2, ctx2) := Eval(rhs, ctxp, FUEL);
    var args: List<Value> := ${cons_args};
    ${invariant}(ctx1, ctx2, addr1.addr, addr2.addr) &&
    HavocPostcondition("${method}", args, ctx1, ctx2, addr1, addr2, ${invariant}, objs1, objs2)
{
    var prefix := ${prefix};
    var ctxp := Eval(prefix, EmptyContext(), FUEL).1;
    var lhs := ${lhs};
    var rhs := ${rhs};
    var (addr1, ctx1) := Eval(lhs, ctxp, FUEL);
    var (addr2, ctx2) := Eval(rhs, ctxp, FUEL);
    var args: List<Value> := ${cons_args};

    var ctx1' := ctx1.(objs := objs1);
    var ctx2' := ctx2.(objs := objs2);
    var scope1 := BindArguments(GetMethod(ctx1', addr1.addr, "${method}").args, args);
    var scope2 := BindArguments(GetMethod(ctx2', addr2.addr, "${method}").args, args);
    var (retL, ctxL) := CallMethod("${method}", scope1, addr1.addr, ctx1');
    var (retR, ctxR) := CallMethod("${method}", scope2, addr2.addr, ctx2');

${body}
}
///< END method_proof

///< START equivalence_proof
// Top-level equivalence proof
lemma ${proof}()
  ensures
    var prefix := ${prefix};
    var ctxp := Eval(prefix, EmptyContext(), FUEL).1;
    var lhs := ${lhs};
    var rhs := ${rhs};
    var (addr1, ctx1) := Eval(lhs, ctxp, FUEL);
    var (addr2, ctx2) := Eval(rhs, ctxp, FUEL);
    Equivalent_AllMethods(ctx1, ctx2, addr1, addr2, ${invariant})
{
    var prefix := ${prefix};
    var ctxp := Eval(prefix, EmptyContext(), FUEL).1;
    var lhs := ${lhs};
    var rhs := ${rhs};
    var (addr1, ctx1) := Eval(lhs, ctxp, FUEL);
    var (addr2, ctx2) := Eval(rhs, ctxp, FUEL);

${body}
}
///< END equivalence_proof

///< START lemma_use_args
    // Invoke equivalence proof for method `${method}`
    forall objs1: ObjList, objs2: ObjList | HavocPrecondition(ctx1, ctx2, addr1, addr2, ${invariant}, objs1, objs2)
      ensures forall ${bvs} :: HavocPostcondition("${method}", ${cons_args}, ctx1, ctx2, addr1, addr2, ${invariant}, objs1, objs2)
    {
        forall ${bvs} {
            ${proof}(objs1, objs2, ${args});
        }
    }
///< END lemma_use_args

///< START lemma_use_noargs
    // Invoke equivalence proof for method `${method}`
    forall objs1: ObjList, objs2: ObjList | HavocPrecondition(ctx1, ctx2, addr1, addr2, ${invariant}, objs1, objs2)
      ensures HavocPostcondition("${method}", LNil, ctx1, ctx2, addr1, addr2, ${invariant}, objs1, objs2)
    { 
        ${proof}(objs1, objs2);
    }
///< END lemma_use_noargs