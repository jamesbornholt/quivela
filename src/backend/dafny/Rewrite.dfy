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


// return expr[e1 := e2]
function method RewriteExpr(expr: Expr, e1: Expr, e2: Expr): Expr
    decreases expr, 0
{
    if expr == e1 then e2 else  // this equality is slow
    match expr
    case EVar(_)                   => expr
    case EConst(_)                 => expr
    case ETuple(elts)              => ETuple(RewriteExprSeq(elts, e1, e2))
    case ESeq(ee1, ee2)            => ESeq(RewriteExpr(ee1, e1, e2), RewriteExpr(ee2, e1, e2))
    case ECVar(obj, name, idx)     => ECVar(RewriteExpr(obj, e1, e2), name, RewriteExpr(idx, e1, e2))
    case ENew(locals, body)        => ENew(RewriteExprLocals(locals, e1, e2), RewriteExpr(body, e1, e2))
    case EMethod(name, args, body) => EMethod(name, args, RewriteExpr(body, e1, e2))
    case EAssign(lhs, rhs)         => EAssign(RewriteExpr(lhs, e1, e2), RewriteExpr(rhs, e1, e2))
    case ECall(obj, name, args)    => ECall(RewriteExpr(obj, e1, e2), name, RewriteExprSeq(args, e1, e2))
    case EITE(cnd, thn, els)       => EITE(RewriteExpr(cnd, e1, e2), RewriteExpr(thn, e1, e2), RewriteExpr(els, e1, e2))
    case ENop()                    => expr
}

function method RewriteExprSeq(exprs: List<Expr>, e1: Expr, e2: Expr): List<Expr>
    decreases exprs
{
    if exprs.LNil? then LNil() else
    Cons(RewriteExpr(exprs.car, e1, e2), RewriteExprSeq(exprs.cdr, e1, e2))
}

function method RewriteExprLocals(locals: List<Init>, e1: Expr, e2: Expr): List<Init>
    decreases locals
{
    if locals.LNil? then LNil() else
    var l := locals.car;
    Cons(Init(l.name, RewriteExpr(l.val, e1, e2)), RewriteExprLocals(locals.cdr, e1, e2))
}
