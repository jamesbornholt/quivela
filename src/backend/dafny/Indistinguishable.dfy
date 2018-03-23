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

include "Lang.dfy"
include "Call.dfy"
include "Rewrite.dfy"



type ContextEquivalence = (Context, Context, Addr, Addr) -> bool

predicate EqualKeys<T(==,!new), U>(l1: List<Pair<T, U>>, l2: List<Pair<T, U>>)
    // ensures forall k :: AssocGet(l1, k).Some? == AssocGet(l2, k).Some?  // probably need a lemma for this
{
    (l1.LNil? && l2.LNil?) ||
    (l1.Cons? && l2.Cons? && l1.car.car == l2.car.car && EqualKeys(l1.cdr, l2.cdr))
}

lemma {:induction l1, l2} EqualKeys_AssocGet<T(==,!new), U>(l1: List<Pair<T, U>>, l2: List<Pair<T, U>>, k: T)
  requires EqualKeys(l1, l2)
  ensures AssocGet(l1, k).Some? <==> AssocGet(l2, k).Some?
{

}

predicate {:induction false} HavocPrecondition(
    ctx1: Context, ctx2: Context, 
    addr1: Value, addr2: Value, 
    Inv: ContextEquivalence,
    objs1: ObjList, objs2: ObjList)
{
    addr1.Ref? && addr2.Ref? &&
    ValidRef(addr1.addr, ctx1) &&
    ValidRef(addr2.addr, ctx2) &&
    Inv(ctx1, ctx2, addr1.addr, addr2.addr) &&
    var ctx1' := ctx1.(objs := objs1);
    var ctx2' := ctx2.(objs := objs2);
    EqualKeys(ctx1.objs, objs1) &&
    EqualKeys(ctx2.objs, objs2) &&
    (forall k: Addr :: AssocGet(ctx1.objs, k).Some? && AssocGet(objs1, k).Some? ==> EqualKeys(AssocGet(ctx1.objs, k).val.locals, AssocGet(objs1, k).val.locals)) &&
    (forall k: Addr :: AssocGet(ctx2.objs, k).Some? && AssocGet(objs2, k).Some? ==> EqualKeys(AssocGet(ctx2.objs, k).val.locals, AssocGet(objs2, k).val.locals)) &&
    (forall k, l :: AssocGet(objs1, k).Some? && AssocGet(AssocGet(objs1, k).val.locals, l).Some? ==> AssocGet(AssocGet(objs1, k).val.locals, l).val != Nil && (AssocGet(AssocGet(objs1, k).val.locals, l).val.Ref? ==> AssocGet(AssocGet(objs1, k).val.locals, l).val.addr < addr1.addr)) &&
    (forall k, l :: AssocGet(objs2, k).Some? && AssocGet(AssocGet(objs2, k).val.locals, l).Some? ==> AssocGet(AssocGet(objs2, k).val.locals, l).val != Nil && (AssocGet(AssocGet(objs2, k).val.locals, l).val.Ref? ==> AssocGet(AssocGet(objs2, k).val.locals, l).val.addr < addr2.addr)) &&
    Inv(ctx1', ctx2', addr1.addr, addr2.addr)
}

predicate {:induction false} HavocPostcondition(
    m: Var, values: List<Value>, 
    ctx1: Context, ctx2: Context, 
    addr1: Value, addr2: Value, 
    Inv: ContextEquivalence,
    objs1': ObjList, objs2': ObjList)
    requires addr1.Ref? && addr2.Ref?
    requires ValidRef(addr1.addr, ctx1)
    requires ValidRef(addr2.addr, ctx2)
    requires ValidMethod(ctx1, addr1.addr, m)
    requires ValidMethod(ctx2, addr2.addr, m)
    requires Length(GetMethod(ctx1, addr1.addr, m).args) == Length(GetMethod(ctx2, addr2.addr, m).args) == Length(values)
    requires Inv(ctx1, ctx2, addr1.addr, addr2.addr)
{
    var ctx1' := ctx1.(objs := objs1');
    var ctx2' := ctx2.(objs := objs2');
    var scope1 := BindArguments(GetMethod(ctx1', addr1.addr, m).args, values);
    var scope2 := BindArguments(GetMethod(ctx2', addr2.addr, m).args, values);
    var (retL, ctxL) := CallMethod(m, scope1, addr1.addr, ctx1');
    var (retR, ctxR) := CallMethod(m, scope2, addr2.addr, ctx2');
    retL == retR && Inv(ctxL, ctxR, addr1.addr, addr2.addr)
}

predicate {:induction false} Equivalent_Method(
    m: Var, values: List<Value>, 
    ctx1: Context, ctx2: Context, 
    addr1: Value, addr2: Value, 
    Inv: ContextEquivalence)
    requires addr1.Ref? && addr2.Ref?
    requires ValidRef(addr1.addr, ctx1)
    requires ValidRef(addr2.addr, ctx2)
    requires ValidMethod(ctx1, addr1.addr, m)
    requires ValidMethod(ctx2, addr2.addr, m)
    requires Length(GetMethod(ctx1, addr1.addr, m).args) == Length(GetMethod(ctx2, addr2.addr, m).args) == Length(values)
    requires Inv(ctx1, ctx2, addr1.addr, addr2.addr)
{
    forall objs1': ObjList, objs2': ObjList ::
    HavocPrecondition(ctx1, ctx2, addr1, addr2, Inv, objs1', objs2')
    ==>
    HavocPostcondition(m, values, ctx1, ctx2, addr1, addr2, Inv, objs1', objs2')
}


predicate {:induction false} Equivalent_AllMethods(ctx1: Context, ctx2: Context, addr1: Value, addr2: Value, Inv: ContextEquivalence)
{
    addr1.Ref? && addr2.Ref? &&
    ValidRef(addr1.addr, ctx1) &&
    ValidRef(addr2.addr, ctx2) &&
    Inv(ctx1, ctx2, addr1.addr, addr2.addr) &&
    forall objs1: ObjList, objs2: ObjList ::
        HavocPrecondition(ctx1, ctx2, addr1, addr2, Inv, objs1, objs2) ==>
        forall m: Var ::
            ValidMethod(ctx1, addr1.addr, m) && ValidMethod(ctx2, addr2.addr, m) &&
            Length(GetMethod(ctx1, addr1.addr, m).args) == Length(GetMethod(ctx2, addr2.addr, m).args) ==>
            forall values: List<Value> ::
                Length(values) == Length(GetMethod(ctx1, addr1.addr, m).args) ==>
                HavocPostcondition(m, values, ctx1, ctx2, addr1, addr2, Inv, objs1, objs2)
}

predicate Equivalent(e1: Expr, e2: Expr, ctx: Context, Inv: ContextEquivalence)
{
    var (ret1, ctx1) := Eval(e1, ctx, FUEL);
    var (ret2, ctx2) := Eval(e2, ctx, FUEL);

    ret1.Ref? && ValidRef(ret1.addr, ctx1) &&
    ret2.Ref? && ValidRef(ret2.addr, ctx2) &&
    Inv(ctx1, ctx2, ret1.addr, ret2.addr) &&
    Equivalent_AllMethods(ctx1, ctx2, ret1, ret2, Inv)
}


predicate ValidRewrite(ctx: Expr, e1: Expr, e2: Expr, lhs: Expr, rhs: Expr, assumptions: seq<(Expr, Expr)>)
{
    (lhs, rhs) in assumptions &&
    var e1' := RewriteExpr(e1, lhs, rhs);
    e1' == e2
}


predicate DefaultInvariant(ctx1: Context, ctx2: Context, addr1: Addr, addr2: Addr)
{
    ValidRef(addr1, ctx1) && ValidRef(addr2, ctx2) &&
    var obj1 := AssocGet(ctx1.objs, addr1).val;
    var obj2 := AssocGet(ctx2.objs, addr2).val;
    forall k :: AssocGet(obj1.locals, k) == AssocGet(obj2.locals, k)
}
