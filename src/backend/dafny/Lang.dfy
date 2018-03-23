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

datatype Value = Int(val: int) | Tuple(elts:List<Value>) | Map(vals: List<Pair<Value, Value>>) | Ref(addr: Addr) | Nil() | Error()

type Var = string
datatype Init = Init(name: Var, val: Expr)

// lists
datatype List<T> = Cons(car: T, cdr: List<T>) | LNil
predicate method InList<T(==)>(l: List<T>, x: T) 
    decreases l
{
    if l.LNil? then false else
    x == l.car || InList(l.cdr, x)
}
function method Length<T>(l: List<T>): nat 
    decreases l
{
    if l.LNil? then 0 else 1 + Length(l.cdr)
}
datatype Option<T> = Some(val: T) | None
function method ListRef<T>(l: List<T>, i: int): Option<T>
    decreases l
{
    if l.LNil? then None else
    if i == 0 then Some(l.car) else ListRef(l.cdr, i-1)
}
lemma lemma_List_Length_Cons<T>(l: List<T>)
    requires Length(l) >= 2
    ensures l.Cons? && l.cdr.Cons?
{}

// association lists
datatype Pair<T,U> = Pair(car: T, cdr: U)
// predicate method InAssocList<T(==),U>(l: List<Pair<T,U>>, x: T)
//     decreases l
// {
//     if l.LNil? then false else
//     l.car.car == x || InAssocList(l.cdr, x)
// }
function method AssocGet<T(==),U>(l: List<Pair<T,U>>, x: T): Option<U>
    decreases l
{
    if l.LNil? then None else
    if l.car.car == x then Some(l.car.cdr) else 
    AssocGet(l.cdr, x)
}
function method AssocSet<T(==),U>(l: List<Pair<T,U>>, x: T, v: U): List<Pair<T,U>>
{
    Cons(Pair(x, v), l)
}

datatype Triple<T,U,V> = Triple(a: T, b: U, c: V)


datatype Expr = EVar(name: Var)
              | EConst(val: Value)
              | ETuple(vals: List<Expr>)
              | ESeq(e1: Expr, e2: Expr)
              | ECVar(obj: Expr, name: Var, idx: Expr)  // compound var obj.name[idx]
              | ENew(locals: List<Init>, body: Expr)
              | EMethod(name: Var, args: List<Var>, body: Expr)
              | EAssign(lhs: Expr, rhs: Expr)
              | ECall(cobj: Expr, cname: Var, cargs: List<Expr>)
              | EITE(cond: Expr, thn: Expr, els: Expr)
              | ENop()


type Scope = List<Pair<Var, Value>>
type Env = List<Pair<Var, Value>>
type ObjList = List<Pair<Addr, Object>>
type MethodList = List<Pair<Var, Method>>
type MethodMap = List<Pair<Addr, MethodList>>

// scope: method-local variables
// objs: global memory
// ths: current object hosting a method call
datatype Context = Context(scope: Scope, objs: ObjList, methods: MethodMap, ths: Addr, nextAddr: Addr)
datatype Object = Object(locals: Env)
datatype Method = Method(name: Var, args: List<Var>, body: Expr)

// Get a fresh new address
type Addr = nat
function method Alloc(ctx: Context): Addr {
    ctx.nextAddr
}
predicate method ValidRef(ref: Addr, ctx: Context)
{
    AssocGet(ctx.objs, ref).Some? && AssocGet(ctx.methods, ref).Some?
}

function method ParseMethods(ms: seq<Method>): map<Var, Method> {
    ParseMethods'(ms, map[])
}
function method ParseMethods'(ms: seq<Method>, mp: map<Var, Method>): map<Var, Method>
    decreases ms
{
    if |ms| == 0 then mp else ParseMethods'(ms[1..], mp[ms[0].name := ms[0]])
}


function method Append<T>(a: List<T>, b: List<T>): List<T>
    decreases a
{
    if a.LNil? then b else Cons(a.car, Append(a.cdr, b))
}

function method InitLocals(locals: List<Init>, ctx: Context, fuel: Fuel, acc: Env): Pair<Context, Env>
    decreases fuel, 3, locals
{
    if locals.LNil? then Pair(ctx, acc) else
    var l := locals.car;
    var oldScope := ctx.scope;
    var ctx_ := ctx.(scope := Append(acc, oldScope));
    if l.val == EConst(Nil()) then
        var (ret, ctx') := Eval_Var(EVar(l.name), ctx_, fuel);
        InitLocals(locals.cdr, ctx'.(scope := oldScope), fuel, AssocSet(acc, l.name, ret))
    else
        var (eval, ctx') := Eval(l.val, ctx_, fuel);
        InitLocals(locals.cdr, ctx'.(scope := oldScope), fuel, AssocSet(acc, l.name, eval))
}


function method EvalArgs(names: List<Var>, exprs: List<Expr>, ctx: Context, fuel: Fuel, acc: Scope): (Scope, Context) 
    requires Length(names) == Length(exprs)
    decreases fuel, 3, exprs
{
    if names.LNil? then (acc, ctx) else 
    var (val, newCtx) := Eval(exprs.car, ctx, fuel);
    EvalArgs(names.cdr, exprs.cdr, newCtx, fuel, Cons(Pair(names.car, val), acc))
}


function method EvalTupleElts(exprs: List<Expr>, ctx: Context, fuel: Fuel): (List<Value>, Context) 
    decreases fuel, 3, exprs
{
    if exprs.LNil? then (LNil, ctx) else 
    var (val, newCtx) := Eval(exprs.car, ctx, fuel);
    var (cdr, ctx') := EvalTupleElts(exprs.cdr, newCtx, fuel);
    (Cons(val, cdr), ctx')
}


function method Eval_Var(e: Expr, ctx: Context, fuel: Fuel): (Value, Context)
    requires e.EVar?
{
    var n := e.name;
    var ret := AssocGet(ctx.scope, n);
    if ret.Some? then
        (ret.val, ctx)
    else if ValidRef(ctx.ths, ctx) && AssocGet(AssocGet(ctx.objs, ctx.ths).val.locals, n).Some? then
        (AssocGet(AssocGet(ctx.objs, ctx.ths).val.locals, n).val, ctx)
    else if ValidRef(0, ctx) && AssocGet(AssocGet(ctx.objs, 0).val.locals, n).Some? then
        (AssocGet(AssocGet(ctx.objs, 0).val.locals, n).val, ctx)
    else (Error(), ctx)
}

function method Eval_Tuple(e: Expr, ctx: Context, fuel: Fuel): (Value, Context)
    requires e.ETuple?
    decreases fuel, 3
{
    var (elts, ctx1) := EvalTupleElts(e.vals, ctx, fuel);
    if InList(elts, Error()) then (Error(), ctx1)
    else (Tuple(elts), ctx1)
}

function method Eval_Seq(e: Expr, ctx: Context, fuel: Fuel): (Value, Context)
    requires e.ESeq?
    decreases fuel, 3
{
    var e1 := e.e1; var e2 := e.e2;
    var (v1, ctx1) := Eval(e1, ctx, fuel);
    Eval(e2, ctx1, fuel)
}

function method Eval_CVar(e: Expr, ctx: Context, fuel: Fuel): (Value, Context)
    requires e.ECVar?
    decreases fuel, 3
{
    var obj := e.obj; var name := e.name; var idx := e.idx;
    var (vobj, ctx') := Eval(obj, ctx, fuel);
    if vobj.Tuple? then
        var (vidx, ctx'') := Eval(idx, ctx', fuel);
        if vidx.Int? && vidx.val >= 0 && vidx.val < Length(vobj.elts) then
            var ret := ListRef(vobj.elts, vidx.val);
            if ret.Some? then (ret.val, ctx'') else (Error(), ctx'')
        else (Error(), ctx'')
    else if !vobj.Ref? && AssocGet(ctx'.scope, name).Some? then
        var ret := AssocGet(ctx'.scope, name).val;
        var vidx := Eval(idx, ctx', fuel).0;
        if vidx.Nil? then
            (ret, ctx')
        else if ret.Map? && AssocGet(ret.vals, vidx).Some? then
            (AssocGet(ret.vals, vidx).val, ctx')
        else (Error(), ctx')
    else
    var base := if vobj.Ref? then 
                    if ValidRef(vobj.addr, ctx') then AssocGet(ctx'.objs, vobj.addr).val.locals else LNil
                else if ValidRef(ctx'.ths, ctx') && AssocGet(AssocGet(ctx'.objs, ctx'.ths).val.locals, name).Some? then
                    AssocGet(ctx'.objs, ctx'.ths).val.locals
                else if ValidRef(0, ctx') && AssocGet(AssocGet(ctx'.objs, 0).val.locals, name).Some? then
                    AssocGet(ctx'.objs, 0).val.locals
                else LNil;
    if AssocGet(base, name).Some? then
        var ret := AssocGet(base, name).val;
        var (vidx, ctx'') := Eval(idx, ctx', fuel);
        if vidx.Nil? then
            (ret, ctx'')
        else if ret.Map? && AssocGet(ret.vals, vidx).Some? then
            (AssocGet(ret.vals, vidx).val, ctx'')
        else (Error(), ctx'')
    else (Error(), ctx')
}

function method Eval_New(e: Expr, ctx: Context, fuel: Fuel): (Value, Context)
    requires e.ENew?
    decreases fuel, 3
{
    var locals := e.locals; var body := e.body;
    var ret := InitLocals(e.locals, ctx, fuel, LNil);
    var ctx' := ret.car; var vlocals := ret.cdr;
    var oldThs := ctx'.ths;
    var oldScope := ctx'.scope;
    var addr := ctx'.nextAddr;
    var ctx'' := ctx'.(objs := AssocSet(ctx'.objs, addr, Object(vlocals)), methods := AssocSet(ctx'.methods, addr, LNil), nextAddr := ctx'.nextAddr + 1, ths := addr);
    var (ret, ctx''') := Eval(e.body, ctx'', fuel);
    (Ref(addr), ctx'''.(ths := oldThs, scope := oldScope))
}

function method Eval_Method(e: Expr, ctx: Context, fuel: Fuel): (Value, Context)
    requires e.EMethod?
    decreases fuel, 3
{
    if ValidRef(ctx.ths, ctx) then
        var obj := AssocGet(ctx.objs, ctx.ths).val;
        var mtd := Method(e.name, e.args, e.body);
        var mtds := AssocGet(ctx.methods, ctx.ths).val;
        (Nil(), ctx.(methods := AssocSet(ctx.methods, ctx.ths, AssocSet(mtds, e.name, mtd))))
    else (Error(), ctx)
}

function method Eval_Assign(e: Expr, ctx: Context, fuel: Fuel): (Value, Context)
    requires e.EAssign?
    decreases fuel, 3
{
    var lhs := e.lhs; var rhs := e.rhs;
    var (erhs, ctx') := Eval(rhs, ctx, fuel);
    // plain Var on the LHS; just set it in the right scope
    if lhs.EVar? then
        if AssocGet(ctx.scope, lhs.name).Some? then  // already a local
            (erhs, ctx'.(scope := AssocSet(ctx'.scope, lhs.name, erhs)))
        else if ValidRef(ctx.ths, ctx) && AssocGet(AssocGet(ctx.objs, ctx.ths).val.locals, lhs.name).Some? then  // already a field
            var me := AssocGet(ctx.objs, ctx.ths).val;
            (erhs, ctx'.(objs := AssocSet(ctx'.objs, ctx.ths, Object(AssocSet(me.locals, lhs.name, erhs)))))
        else if ValidRef(0, ctx) && AssocGet(AssocGet(ctx.objs, 0).val.locals, lhs.name).Some? then  // already a global
            var me := AssocGet(ctx.objs, 0).val;
            (erhs, ctx'.(objs := AssocSet(ctx'.objs, 0, Object(AssocSet(me.locals, lhs.name, erhs)))))
        else if ValidRef(ctx.ths, ctx) && ctx.ths != 0 then  // inside a method call, restrict the scope
            (erhs, ctx'.(scope := AssocSet(ctx'.scope, lhs.name, erhs)))
        else if ValidRef(0, ctx) then  // outside a method call, everything is global
            var me := AssocGet(ctx.objs, 0).val;
            (erhs, ctx'.(objs := AssocSet(ctx'.objs, 0, Object(AssocSet(me.locals, lhs.name, erhs)))))
        else (Error(), ctx')
    // compound var on the LHS
    else if lhs.ECVar? then
        var (eobj, ctx'') := Eval(lhs.obj, ctx', fuel);
        var (eidx, ctx''') := Eval(lhs.idx, ctx'', fuel);
        if eobj.Error? then (Error(), ctx''')
        else if eidx.Error? then (Error(), ctx''')
        // is the LHS a reference to an object?
        else if eobj.Ref? then
            if !ValidRef(eobj.addr, ctx''') then (Error(), ctx''') else
            var base := AssocGet(ctx'''.objs, eobj.addr).val;
            // are we setting an index in a map?
            if eidx.Nil? then
                (erhs, ctx'''.(objs := AssocSet(ctx'''.objs, eobj.addr, Object(AssocSet(base.locals, lhs.name, erhs)))))
            // we might need to convert the current value to a map
            else var baseMap := if AssocGet(base.locals, lhs.name).Some? && AssocGet(base.locals, lhs.name).val.Map? then AssocGet(base.locals, lhs.name).val.vals else LNil;
                 var newObj := Object(AssocSet(base.locals, lhs.name, Map(Cons(Pair(eidx, erhs), baseMap))));
                 (erhs, ctx'''.(objs := AssocSet(ctx'''.objs, eobj.addr, newObj)))
        else if eobj.Nil? then // LHS is not a ref
            if eidx.Nil? then
                if AssocGet(ctx'''.scope, lhs.name).Some? then  // already a local
                    (erhs, ctx'''.(scope := AssocSet(ctx'''.scope, lhs.name, erhs)))
                else if ValidRef(ctx'''.ths, ctx''') && AssocGet(AssocGet(ctx'''.objs, ctx'''.ths).val.locals, lhs.name).Some? then  // already a field
                    var me := AssocGet(ctx'''.objs, ctx'''.ths).val;
                    (erhs, ctx'''.(objs := AssocSet(ctx'''.objs, ctx'''.ths, Object(AssocSet(me.locals, lhs.name, erhs)))))
                else if ValidRef(0, ctx''') && AssocGet(AssocGet(ctx'''.objs, 0).val.locals, lhs.name).Some? then  // already a global
                    var me := AssocGet(ctx'''.objs, 0).val;
                    (erhs, ctx'''.(objs := AssocSet(ctx'''.objs, 0, Object(AssocSet(me.locals, lhs.name, erhs)))))
                else if ValidRef(ctx'''.ths, ctx''') then  // inside a method call, restrict the scope
                    (erhs, ctx'''.(scope := AssocSet(ctx'''.scope, lhs.name, erhs)))
                else (Error(), ctx''')
            else if AssocGet(ctx'''.scope, lhs.name).Some? then  // already a local
                var baseMap := if AssocGet(ctx'''.scope, lhs.name).val.Map? then AssocGet(ctx'''.scope, lhs.name).val.vals else LNil;
                (erhs, ctx'''.(scope := AssocSet(ctx'''.scope, lhs.name, Map(Cons(Pair(eidx, erhs), baseMap)))))
            else if ValidRef(ctx'''.ths, ctx''') && AssocGet(AssocGet(ctx'''.objs, ctx'''.ths).val.locals, lhs.name).Some? then  // already a field
                var me := AssocGet(ctx'''.objs, ctx'''.ths).val;
                var baseMap := if AssocGet(me.locals, lhs.name).val.Map? then AssocGet(me.locals, lhs.name).val.vals else LNil;
                var newMap := Map(Cons(Pair(eidx, erhs), baseMap));
                (erhs, ctx'''.(objs := AssocSet(ctx'''.objs, ctx'''.ths, Object(AssocSet(me.locals, lhs.name, newMap)))))
            else if ValidRef(0, ctx''') && AssocGet(AssocGet(ctx'''.objs, 0).val.locals, lhs.name).Some? then  // already a global
                var me := AssocGet(ctx'''.objs, 0).val;
                var baseMap := if AssocGet(me.locals, lhs.name).val.Map? then AssocGet(me.locals, lhs.name).val.vals else LNil;
                var newMap := Map(Cons(Pair(eidx, erhs), baseMap));
                (erhs, ctx'''.(objs := AssocSet(ctx'''.objs, 0, Object(AssocSet(me.locals, lhs.name, newMap)))))
            // note: no default case; the variable must already exist to do a map assignment to it
            else (Error(), ctx''')  // the variable doesn't exist in any reachable scope, so we can't update an index at it
        else (Error(), ctx''')  // LHS was not valid  
    else (Error(), ctx)
}

function method Call_With_Scope(body: Expr, ctx: Context, scope: Scope, ths: Addr, fuel: Fuel): (Value, Context)
    decreases fuel, 1
{
    var oldThis := ctx.ths;
    var oldScope := ctx.scope;
    var (ret, ctx') := Eval(body, ctx.(scope := scope, ths := ths), fuel);
    (ret, ctx'.(scope := oldScope, ths := oldThis))
}

function method Call_Builtin_Binop(name: Var, args: List<Expr>, ctx: Context, fuel: Fuel): (Value, Context)
    requires Length(args) == 2
    decreases fuel, 1
{
    if name == "&" then
        var (a, ctx') := Eval(args.car, ctx, fuel);
        if a.Error? then (a, ctx') else
        //if !a.Int? || a.val == 0 then (Int(0), ctx') else
        lemma_List_Length_Cons(args);
        Eval(args.cdr.car, ctx', fuel)
    else if name == "|" then
        var (a, ctx') := Eval(args.car, ctx, fuel);
        if !a.Error? then (a, ctx') else
        lemma_List_Length_Cons(args);
        Eval(args.cdr.car, ctx', fuel)
    else if name == "==" then
        var (a, ctx') := Eval(args.car, ctx, fuel);
        lemma_List_Length_Cons(args);
        var (b, ctx'') := Eval(args.cdr.car, ctx', fuel);
        (if a == b then Int(1) else Error(), ctx'')
    else
    var (a, ctx') := Eval(args.car, ctx, fuel);
    lemma_List_Length_Cons(args);
    var (b, ctx'') := Eval(args.cdr.car, ctx', fuel);
    if !a.Int? || !b.Int? then (Error(), ctx'') else
    if name == "+" then
        (Int(a.val + b.val), ctx'')
    else if name == "-" then
        (Int(a.val - b.val), ctx'')
    else if name == "*" then
        (Int(a.val * b.val), ctx'')
    else if name == "/" then
        if b.val == 0 then (Error(), ctx'') else
        (Int(a.val / b.val), ctx'')
    else if name == "<" then
        (Int(if a.val < b.val then 1 else 0), ctx'')
    else if name == ">" then
        (Int(if a.val > b.val then 1 else 0), ctx'')
    else (Error(), ctx'')
}

function method Call_Builtin_Unop(name: Var, args: List<Expr>, ctx: Context, fuel: Fuel): (Value, Context)
    requires Length(args) == 1
    decreases fuel, 1
{
    var (a, ctx') := Eval(args.car, ctx, fuel);
    if name == "!" then
        (if a.Error? then Int(1) else Error(), ctx')
    else (Error(), ctx)
}

function method Call_Builtin(name: Var, args: List<Expr>, ctx: Context, fuel: Fuel): (Value, Context)
    decreases fuel, 2
{
    var arity := Is_Builtin_Arity(name);
    if arity != Length(args) then (Error(), ctx) else
    if arity == 2 then Call_Builtin_Binop(name, args, ctx, fuel)
    else if arity == 1 then Call_Builtin_Unop(name, args, ctx, fuel)
    else (Error(), ctx)
}

function method Is_Builtin_Arity(name: Var): int
{
    if name == "+" || name == "-" || name == "*" || name == "/" || 
       name == "<" || name == ">" || name == "==" || name == "&" || name == "|" then
        2
    else if name == "!" then
        1
    else -1
}

function method Eval_Call(e: Expr, ctx: Context, fuel: Fuel): (Value, Context)
    requires e.ECall?
    decreases fuel, 3
{
    var obj := e.cobj; var name := e.cname; var args: List<Expr> := e.cargs;
    var (eref, ctx') := Eval(obj, ctx, fuel);
    if eref.Ref? then
        if !ValidRef(eref.addr, ctx') then (Error(), ctx') else
        if AssocGet(AssocGet(ctx'.methods, eref.addr).val, name).None? then (Error(), ctx') else
        var mtd := AssocGet(AssocGet(ctx'.methods, eref.addr).val, name).val;
        if Length(mtd.args) != Length(args) then (Error(), ctx') else
        var (scope, ctx'') := EvalArgs(mtd.args, args, ctx', fuel, LNil);
        Call_With_Scope(mtd.body, ctx'', scope, eref.addr, fuel)
    else if eref.Nil? then
        // either a builtin call or a method call in current scope
        if Is_Builtin_Arity(name) != -1 then
            Call_Builtin(name, args, ctx', fuel)
        else var baseAddr := if ValidRef(ctx'.ths, ctx') && AssocGet(AssocGet(ctx'.methods, ctx'.ths).val, name).Some? then ctx'.ths else 0;
        if ValidRef(baseAddr, ctx') && AssocGet(AssocGet(ctx'.methods, baseAddr).val, name).Some? then
            var mtd := AssocGet(AssocGet(ctx'.methods, baseAddr).val, name).val;
            if Length(mtd.args) != Length(args) then (Error(), ctx') else
            var (scope, ctx'') := EvalArgs(mtd.args, args, ctx', fuel, LNil);
            Call_With_Scope(mtd.body, ctx'', scope, baseAddr, fuel)
        else
            (Error(), ctx')
    else
        (Error(), ctx')
}

function method Eval_ITE(e: Expr, ctx: Context, fuel: Fuel): (Value, Context)
    requires e.EITE?
    decreases fuel, 3
{
    var cond := e.cond; var thn := e.thn; var els := e.els;
    var (econd, ctx') := Eval(cond, ctx, fuel);
    if econd.Error? || econd.Nil? || (econd.Int? && econd.val == 0) then
        Eval(els, ctx', fuel)
    else
        Eval(thn, ctx', fuel)
}

type Fuel = nat
function method Eval(e: Expr, ctx: Context, fuel: Fuel): (Value, Context)
    decreases fuel, 0
    // ensures ctx.nextAddr !in Eval(e, ctx, fuel).1.objs;
{
    if fuel == 0 then (Error(), ctx) else
    var fuel' := fuel - 1;
    match e
    case EVar(n) => Eval_Var(e, ctx, fuel')
    case EConst(v) => (v, ctx)
    case ETuple(a) => Eval_Tuple(e, ctx, fuel')
    case ESeq(e1, e2) => Eval_Seq(e, ctx, fuel')
    case ECVar(obj, name, idx) => Eval_CVar(e, ctx, fuel')
    case ENew(locals, body) => Eval_New(e, ctx, fuel')
    case EMethod(name, args, body) => Eval_Method(e, ctx, fuel')
    case EAssign(lhs, rhs) => Eval_Assign(e, ctx, fuel')
    case ECall(obj, name, args) => Eval_Call(e, ctx, fuel')
    case EITE(cond, thn, els) => Eval_ITE(e, ctx, fuel')
    case ENop() => (Nil(), ctx)
}


// Dafny needs some reminding that a valid address exists in the empty context
function method EmptyContext(): Context {
    Context(LNil, Cons(Pair(0, Object(LNil)), LNil), Cons(Pair(0, LNil), LNil), 0, 1)
}
function method Eval_EmptyContext(e: Expr): Value {
    Eval(e, EmptyContext(), 20).0
}
