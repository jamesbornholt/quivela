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


// datatype Value = Int(val: int) 
//                | Tuple(elts: seq<Value>) 
//                | Map(vals: map<Value, Value>) 
//                | Ref(addr: Addr) 
//                | Nil() 
//                | Error()

// type Var = string
// datatype Init = Init(name: Var, val: Expr)
// datatype Method = Method(name: Var, args: seq<Var>, body: Expr)

// datatype Expr = EVar(name: Var)
//               | EConst(val: Value)
//               | ESeq(e1: Expr, e2: Expr)
//               | ECVar(obj: Expr, name: Var, idx: Expr)  // compound var obj.name[idx]
//               | ENew(locals: seq<Init>, body: seq<Method>)
//               | EClass(clname: Var, clargs: seq<Var>, clobj: Expr)
//               | EAssign(lhs: Expr, rhs: Expr)
//               | ECall(cobj: Expr, cname: Var, cargs: seq<Expr>)
//               | EITE(cond: Expr, thn: Expr, els: Expr)
//               | ENop()

method Reflect_Value(v: Value)
    decreases v
{
    if v.Int? {
        print v.val;
    } else if v.Ref? {
        print "Ref(";
        print v.addr;
        print ")";
    } else if v.Tuple? {
        print "<";
        var i := v.elts;
        while i.Cons?
            decreases i
        {
            Reflect_Value(i.car);
            i := i.cdr;
            if i.Cons? {
                print ", ";
            }
        }
        print ">";
    } else if v.Nil? {
        print "nil";
    } else if v.Error? {
        print "error";
    } else {
        print v;
    }
}

method Reflect_Expr(e: Expr)
    decreases e
{
    if e.EVar? {
        print e.name;
    } else if e.EConst? {
        Reflect_Value(e.val);
    } else if e.ETuple? {
        print "<";
        var i := e.vals;
        while i.Cons?
            decreases i
        {
            Reflect_Expr(i.car);
            i := i.cdr;
            if i.Cons? {
                print ", ";
            }
        }
        print ">";
    } else if e.ESeq? {
        Reflect_Expr(e.e1);
        print "; ";
        Reflect_Expr(e.e2);
    } else if e.ECVar? {
        if e.obj != EConst(Nil()) {
            Reflect_Expr(e.obj);
            print ".";
        }
        print e.name;
        if e.idx != EConst(Nil()) {
            print "[";
            Reflect_Expr(e.idx);
            print "]";
        }
    } else if e.ENew? {
        print "new (";
        var i := e.locals;
        while i.Cons?
            decreases i
        {
            var l := i.car;
            print l.name;
            if l.val != EConst(Nil()) {
                print "=";
                Reflect_Expr(l.val);
            }
            i := i.cdr;
            if i.Cons? {
                print ", ";
            }
        }
        print ") { ";
        var j := 0;
        Reflect_Expr(e.body);
        print " }; ";
    } else if e.EMethod? {
        print e.name;
        print "(";
        var i := e.args;
        while i.Cons?
            decreases i
        {
            print i.car;
            i := i.cdr;
            if i.Cons? {
                print ", ";
            }
        }
        print ") { ";
        var j := 0;
        Reflect_Expr(e.body);
        print " }; ";
    } else if e.EAssign? {
        Reflect_Expr(e.lhs);
        print " = ";
        Reflect_Expr(e.rhs);
    } else if e.ECall? {
        // could be an infix call
        if e.cobj == EConst(Nil()) && Is_Builtin_Arity(e.cname) != -1 {
            var arity := Is_Builtin_Arity(e.cname);
            if arity == 1 && Length(e.cargs) > 0 {
                print e.cname;
                Reflect_Expr(e.cargs.car);
            } else if arity == 2 && Length(e.cargs) > 1 {
                Reflect_Expr(e.cargs.car);
                print " ";
                print e.cname;
                print " ";
                lemma_List_Length_Cons(e.cargs);
                Reflect_Expr(e.cargs.cdr.car);
            }
        } else {
            if e.cobj != EConst(Nil()) {
                Reflect_Expr(e.cobj);
                print ".";
            }
            print e.cname;
            print "(";
            var i := e.cargs;
            while i.Cons?
                decreases i
            {
                Reflect_Expr(i.car);
                i := i.cdr;
                if i.Cons? {
                    print ", ";
                }
            }
            print ")";
        }
    } else if e.EITE? {
        print "if ";
        Reflect_Expr(e.cond);
        print " { ";
        Reflect_Expr(e.thn);
        print " } ";
        if (e.els != ENop()) {
            print "else { ";
            Reflect_Expr(e.els);
            print " }";
        }
    }
}