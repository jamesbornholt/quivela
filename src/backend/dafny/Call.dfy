include "Lang.dfy"

const FUEL := 10;

predicate ValidMethod(ctx: Context, ths: nat, name: Var) {
    AssocGet(ctx.methods, ths).Some? && AssocGet(AssocGet(ctx.methods, ths).val, name).Some?
}

function method GetMethod(ctx: Context, ths: nat, name: Var): Method
    requires ValidMethod(ctx, ths, name)
{
    AssocGet(AssocGet(ctx.methods, ths).val, name).val
}

function method CallMethod(name: Var, scope: Scope, ths: nat, ctx: Context): (Value, Context)
    requires ValidMethod(ctx, ths, name)
{
    Call_With_Scope(AssocGet(AssocGet(ctx.methods, ths).val, name).val.body, ctx, scope, ths, FUEL)
}

function method BindArguments(names: List<Var>, values: List<Value>): Scope
    requires Length(names) == Length(values)
    decreases names
{
    if names.LNil? then LNil else Cons(Pair(names.car, values.car), BindArguments(names.cdr, values.cdr))
}