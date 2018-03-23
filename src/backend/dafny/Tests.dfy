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
include "Refl.dfy"


function method TestContext(n: Var, v: Value): Context {
    EmptyContext().(objs := AssocSet(EmptyContext().objs, 0, Object(Cons(Pair(n, v), LNil))))
}
function method TestContext_Object1(obj: Object): Context {
    EmptyContext().(objs := AssocSet(EmptyContext().objs, 1, obj), methods := AssocSet(EmptyContext().methods, 1, LNil), nextAddr := 2)
}
function method TestObject(n: Var, v: Value): Object {
    Object(Cons(Pair(n, v), LNil))
}



method Tests() {
    var FUEL := 20;

    // 5
    var Test_Const := EConst(Int(5));
    assert Eval_EmptyContext(Test_Const) == Int(5);

    // x
    var Test_Var := EVar("x");
    assert Eval(Test_Var, TestContext("x", Int(5)), FUEL).0 == Int(5);

    // 5; 6
    var Test_Seq := ESeq(EConst(Int(5)), EConst(Int(6)));
    assert Eval_EmptyContext(Test_Seq) == Int(6);

    // x[1]
    var Test_CVar_Idx := ECVar(EConst(Nil()), "x", EConst(Int(1)));
    var Test_CVar_Idx_env := TestContext("x", Map(Cons(Pair(Int(1), Int(2)), LNil)));
    assert Eval(Test_CVar_Idx, Test_CVar_Idx_env, FUEL).0 == Int(2);

    // 1.x
    var Test_CVar_Obj := ECVar(EConst(Ref(1)), "x", EConst(Nil()));
    var Test_CVar_Obj_env := TestContext_Object1(TestObject("x", Int(5)));
    assert Eval(Test_CVar_Obj, Test_CVar_Obj_env, FUEL).0 == Int(5);

    // 1.x[2]
    var Test_CVar_Obj_Idx := ECVar(EConst(Ref(1)), "x", EConst(Int(2)));
    var Test_CVar_Obj_Idx_env := TestContext_Object1(TestObject("x", Map(Cons(Pair(Int(2), Int(5)), LNil))));
    assert Eval(Test_CVar_Obj_Idx, Test_CVar_Obj_Idx_env, FUEL).0 == Int(5);

    // x = 5
    var Test_Assign_Var := ESeq(EAssign(EVar("x"), EConst(Int(5))), EVar("x"));
    assert Eval_EmptyContext(Test_Assign_Var) == Int(5);

    // x = y
    var Test_Assign_Var_Var := ESeq(EAssign(EVar("x"), EVar("y")), EVar("x"));
    assert Eval(Test_Assign_Var_Var, TestContext("y", Int(5)), FUEL).0 == Int(5);

    // x[1] = 5
    var Test_Assign_CVar_Idx := ESeq(EAssign(ECVar(EConst(Nil()), "x", EConst(Int(1))), EConst(Int(5))), 
                                     ECVar(EConst(Nil()), "x", EConst(Int(1))));
    // ... where x is not previously allocated
    assert Eval_EmptyContext(Test_Assign_CVar_Idx).Error?;
    // ... where x is previously a nat
    assert Eval(Test_Assign_CVar_Idx, TestContext("x", Int(0)), FUEL).0 == Int(5);
    // ... where x is already a map
    assert Eval(Test_Assign_CVar_Idx, TestContext("x", Map(Cons(Pair(Int(2), Int(3)), LNil))), FUEL).0 == Int(5);

    // 1.x = 5
    var Test_Assign_CVar_Obj := ESeq(EAssign(ECVar(EConst(Ref(1)), "x", EConst(Nil())), EConst(Int(5))), 
                                     ECVar(EConst(Ref(1)), "x", EConst(Nil())));
    // ... where 1 is not a valid ref
    assert Eval_EmptyContext(Test_Assign_CVar_Obj) == Error();
    // ... where 1 is a valid ref, x is not previously set
    assert Eval(Test_Assign_CVar_Obj, TestContext_Object1(Object(LNil)), FUEL).0 == Int(5);
    // ... where 1 is a valid ref, x is previously set
    assert Eval(Test_Assign_CVar_Obj, TestContext_Object1(TestObject("x", Int(2))), FUEL).0 == Int(5);

    // 1.x[2] = 5
    var Test_Assign_CVar_Obj_Idx := ESeq(EAssign(ECVar(EConst(Ref(1)), "x", EConst(Int(2))), EConst(Int(5))), 
                                         ECVar(EConst(Ref(1)), "x", EConst(Int(2))));
    // ... where 1 is not a valid ref
    assert Eval_EmptyContext(Test_Assign_CVar_Obj_Idx) == Error();
    // ... where 1 is a valid ref, x is not previously allocated
    assert Eval(Test_Assign_CVar_Obj_Idx, TestContext_Object1(Object(LNil)), FUEL).0 == Int(5);
    // ... where 1 is a valid ref, x is previously a nat
    assert Eval(Test_Assign_CVar_Obj_Idx, TestContext_Object1(TestObject("x", Int(6))), FUEL).0 == Int(5);
    // ... where 1 is a valid ref, x is already a map
    assert Eval(Test_Assign_CVar_Obj_Idx, TestContext_Object1(TestObject("x", Map(Cons(Pair(Int(2), Int(3)), LNil)))), FUEL).0 == Int(5);


    // new() {}
    var Test_New_Empty := ENew(LNil(), EConst(Nil()));
    var (ret1, env1) := Eval(Test_New_Empty, EmptyContext(), FUEL);
    assert ret1.Ref?;
    assert Length(env1.objs) == 2;
    assert Length(AssocGet(env1.objs, ret1.addr).val.locals) == 0;

    // new(a=5) {}
    var Test_New_Local := ENew(Cons(Init("a", EConst(Int(5))), LNil()), EConst(Nil()));
    var (ret2, env2) := Eval(Test_New_Local, EmptyContext(), FUEL);
    assert ret2.Ref?;
    assert Length(env2.objs) == 2;
    assert Length(AssocGet(env2.objs, ret2.addr).val.locals) == 1 && AssocGet(AssocGet(env2.objs, ret2.addr).val.locals, "a").val == Int(5);

    // new() { get(b) { b } }
    var Test_New_Method := ENew(LNil(), EMethod("get", Cons("b", LNil()), EVar("b")));
    var (ret3, env3) := Eval(Test_New_Method, EmptyContext(), FUEL);
    assert ret3.Ref?;
    assert Length(env3.objs) == 2;
    assert Length(AssocGet(env3.methods, ret3.addr).val) == 1;
    assert AssocGet(AssocGet(env3.methods, ret3.addr).val, "get").val == Method("get", Cons("b", LNil()), EVar("b"));


    // x = new() { get(b) { b } }; x.get(5)
    var Test_Call_Ret := ESeq(EAssign(EVar("x"), ENew(LNil(), EMethod("get", Cons("b", LNil()), EVar("b")))), ECall(EVar("x"), "get", Cons(EConst(Int(5)), LNil())));
    assert Eval_EmptyContext(Test_Call_Ret) == Int(5);

    // x = new() { get(b) { b } }; x.get()
    var Test_Call_Wrong_Args := ESeq(EAssign(EVar("x"), ENew(LNil(), EMethod("get", Cons("b", LNil()), EVar("b")))), ECall(EVar("x"), "get", LNil()));
    assert Eval_EmptyContext(Test_Call_Wrong_Args) == Error();

    // x = new() { get(b) { b } }; x.foo()
    var Test_Call_Wrong_Name := ESeq(EAssign(EVar("x"), ENew(LNil(), EMethod("get", Cons("b", LNil()), EVar("b")))), ECall(EVar("x"), "foo", LNil()));
    assert Eval_EmptyContext(Test_Call_Wrong_Name) == Error();

    // x = 5; x.foo()
    var Test_Call_Not_Object := ESeq(EAssign(EVar("x"), EConst(Int(5))), ECall(EVar("x"), "foo", LNil()));
    assert Eval_EmptyContext(Test_Call_Not_Object) == Error();


    // ite x 1 2
    var Test_ITE := EITE(EVar("x"), EConst(Int(2)), EConst(Int(3)));
    // ... where x is undefined
    assert Eval_EmptyContext(Test_ITE) == Int(3);
    // ... where x is truthy
    assert Eval(Test_ITE, TestContext("x", Int(1)), FUEL).0 == Int(2);
    // ... where x is falsy
    assert Eval(Test_ITE, TestContext("x", Int(0)), FUEL).0 == Int(3);

    // if x { y := 5 } else { y := 6 }; y
    var Test_ITE_Ctx := ESeq(EITE(EVar("x"), EAssign(EVar("y"), EConst(Int(5))), EAssign(EVar("y"), EConst(Int(6)))),
                                  EVar("y"));
    // ... where x is truthy
    assert Eval(Test_ITE_Ctx, TestContext("x", Int(1)), FUEL).0 == Int(5);
    // ... where x is falsy
    assert Eval(Test_ITE_Ctx, TestContext("x", Int(0)), FUEL).0 == Int(6);

    // if (y = x) { 5 } else { 6 }; y     // note that's 'assign x to y', not a comparison
    var Test_ITE_Cond_Ctx := ESeq(EITE(EAssign(EVar("y"), EVar("x")), EConst(Int(5)), EConst(Int(6))),
                                  EVar("y"));
    // ... where y is truthy
    assert Eval(Test_ITE_Cond_Ctx, TestContext("x", Int(1)), FUEL).0 == Int(1);
    // ... where y is falsy
    assert Eval(Test_ITE_Cond_Ctx, TestContext("x", Int(0)), FUEL).0 == Int(0);

    // 5 + 6
    var Test_Plus_Const := ECall(EConst(Nil()), "+", Cons(EConst(Int(5)), Cons(EConst(Int(6)), LNil())));
    assert Eval(Test_Plus_Const, EmptyContext(), FUEL).0 == Int(11);

}


method Main() {
    // PrfC() {
    //     new (k=rnd()) {
    //         get(m) {
    //             prf(k, m)
    //         }
    //     }
    // }
    var PrfC := ENew(Cons(Init("k", EConst(Int(0))), LNil()),
                  EMethod("get", Cons("m", LNil()),
                    ECall(EConst(Nil()), "prf", Cons(EVar("k"), Cons(EVar("m"), LNil())))));

    Reflect_Expr(PrfC);

    //assert Eval(PrfC) == Nil();

    // PrfI() {
    //     new (v=0) {
    //         get(m) {
    //             if (v[m]) {
    //                 v[m]
    //             } else {
    //                 v[m] = rnd()
    //                 v[m]
    //             }
    //         }
    //     }
    // }
    var PrfI := ENew(Cons(Init("v", EConst(Int(0))), LNil()),
                  EMethod("get", Cons("m", LNil()),
                    EITE(ECVar(EConst(Nil()), "v", EVar("m")),
                         ECVar(EConst(Nil()), "v", EVar("m")),
                         ESeq(EAssign(ECVar(EConst(Nil()), "v", EVar("m")), ECall(EConst(Nil()), "rand", LNil())),
                              ECVar(EConst(Nil()), "v", EVar("m"))))));
    

    Reflect_Expr(PrfI);

}