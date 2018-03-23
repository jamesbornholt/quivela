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

from collections import namedtuple

import ply.lex as lex
import ply.yacc as yacc

from .ast import *

## Lexer ######################################################################

states = [
    ('verbatim', 'exclusive')
]

reserved = {
    'new': "NEW",
    'if': "IF",
    'else': "ELSE",
    'assert': "ASSERT",
    'assume': "ASSUME",
}

tokens = ["IDENT", "NUMBER", "EQ", "COMMENT", "VERBATIM"] + list(reserved.values())

literals = "+-*/=()<>;.[]{},~&!|:*"

def t_IDENT(t):
    r'[a-zA-Z_][a-zA-Z0-9]*'
    t.type = reserved.get(t.value, 'IDENT')
    return t

def t_NUMBER(t):
    r'\d+'
    t.value = int(t.value)
    return t

t_EQ = "=="

def t_COMMENT(t):
    r'//.*'
    pass


def t_VERBSTART(t):
    r'\{\{\{'
    t.lexer.verb_start = t.lexer.lexpos
    t.lexer.level = 3
    t.lexer.begin('verbatim')

def t_verbatim_lbrace(t):     
    r'\{'
    t.lexer.level += 1                

def t_verbatim_rbrace(t):
    r'\}'
    t.lexer.level -= 1
    if t.lexer.level == 0:
         t.value = t.lexer.lexdata[t.lexer.verb_start:t.lexer.lexpos-3]
         t.type = "VERBATIM"
         t.lexer.lineno += t.value.count('\n')
         t.lexer.begin('INITIAL')           
         return t

def t_verbatim_anything(t):
   r'[^\s\{\}]+'

t_verbatim_ignore = " \t\n"

def t_verbatim_error(t):
    t.lexer.skip(1)

t_ignore = " \t"

def t_newline(t):
    r'\n+'
    t.lexer.lineno += len(t.value)


def find_column(token):
    last_cr = lexer.lexdata.rfind("\n", 0, token.lexpos)
    if last_cr < 0:
        last_cr = 0
    column = token.lexpos - last_cr + 1
    return column


def t_error(t):
    print("Illegal character '%s'" % t.value[0])
    t.lexer.skip(1)


lexer = lex.lex()


# for testing only
def lex_string(s):
    lexer.input(s)
    tokens = []
    t = lexer.token()
    while len(tokens) < 200 and t is not None:
        tokens.append(t)
        t = lexer.token()
    return tokens


## Parser #####################################################################

precedence = [
    ('left', '&', '|'),
    ('nonassoc', '='),
    ('nonassoc', '<', '>', 'EQ'),
    ('left', '+', '-'),
    ('left', '*', '/'),
    ('right', 'UNARY'),
    ('left', '.', '[')
]


def p_toplevel(p):
    """toplevel : toplevel_expression_list"""
    p[0] = ('toplevel', p[1])

def p_toplevel_expression_list(p):
    """toplevel_expression_list : toplevel_expression toplevel_expression_list
                                | toplevel_expression ";" toplevel_expression_list
                                | """
    if len(p) == 3:
        assert isinstance(p[2], list)
        p[0] = [p[1]] + p[2]
    elif len(p) == 4:
        assert isinstance(p[3], list)
        p[0] = [p[1]] + p[3]
    else:
        p[0] = []

def p_expression_list(p):
    """expression_list : expression_list expression
                       | expression_list ";" expression
                       | expression
                       | expression_list expression ";"
                       | expression_list ";" expression ";"
                       | expression ";"
                       | """
    if (len(p) == 3 and p[2] != ";") or (len(p) == 4 and p[3] == ";"):
        assert isinstance(p[1], list)
        p[0] = p[1] + [p[2]]
    elif (len(p) == 4 and p[3] != ";") or (len(p) == 5 and p[4] == ";"):
        assert isinstance(p[1], list)
        p[0] = p[1] + [p[3]]
    elif len(p) == 2 or (len(p) == 3 and p[2] == ";"):
        p[0] = [p[1]]
    else:
        p[0] = []

def p_toplevel_expression_expr(p):
    'toplevel_expression : expression'
    p[0] = p[1]

def p_toplevel_expression_proof(p):
    "toplevel_expression : proof"
    p[0] = p[1]

def p_proof(p):
    """proof : proof_term '~' proof_rest
             | proof_term '~' '[' proof_annotation ']' proof_rest
             | proof_term '~' '[' proof_annotation ']' VERBATIM proof_rest"""
    if len(p) == 4:
        p[0] = ('proof', [(p[1], None, "")] + p[3])
    elif len(p) == 7:
        p[0] = ('proof', [(p[1], p[4], "")] + p[6])
    else:
        p[0] = ('proof', [(p[1], p[4], p[6])] + p[7])

def p_proof_term(p):
    "proof_term : expression"
    p[0] = p[1]

def p_proof_rest(p):
    """proof_rest : proof_term '~' proof_rest
                  | proof_term '~' '[' proof_annotation ']' proof_rest
                  | proof_term '~' '[' proof_annotation ']' VERBATIM proof_rest
                  | proof_term"""
    if len(p) == 4:
        p[0] = [(p[1], None, "")] + p[3]
    elif len(p) == 7:
        p[0] = [(p[1], p[4], "")] + p[6]
    elif len(p) == 10:
        p[0] = [(p[1], p[4], p[6])] + p[7]
    else:
        p[0] = [(p[1], None, "")]

def p_toplevel_expression_assert(p):
    "toplevel_expression : ASSERT expression"
    p[0] = ('assert', p[2])

def p_toplevel_expression_assume(p):
    "toplevel_expression : ASSUME proof"
    p[0] = ('assume', p[2])

def p_proof_annotation(p):
    """proof_annotation : expression"""
    p[0] = p[1]

def p_expression_assign(p):
    'expression : lvalue "=" expression'
    p[0] = ('assign', p[1], p[3])

def p_expression_binop(p):
    """expression : expression '+' expression
                  | expression '-' expression
                  | expression '*' expression
                  | expression '/' expression
                  | expression '<' expression
                  | expression '>' expression
                  | expression EQ  expression
                  | expression '&' expression
                  | expression '|' expression"""
    p[0] = ('binop', p[2], p[1], p[3])

def p_expression_uminus(p):
    """expression : '-' expression  %prec UNARY
                  | '+' expression  %prec UNARY
                  | '!' expression  %prec UNARY"""
    p[0] = ('unop', p[1], p[2])

def p_arg(p):
    """arg : expression
           | IDENT ':' type"""
    if len(p) == 2:
        p[0] = p[1]
    else:
        p[0] = ('formal', p[1], p[3])

def p_type(p):
    """type : '*'
            | '<' type type_trailer"""
    if len(p) == 2:
        p[0] = '*'
    else:
        p[0] = tuple([p[2]] + p[3])

def p_type_trailer(p):
    """type_trailer : ',' type type_trailer
                    | '>'"""
    if len(p) == 2:
        p[0] = []
    else:
        p[0] = [p[2]] + p[3]

def p_arglist(p):
    """arglist : arg ',' arglist
               | arg
               | """
    if len(p) == 4:
        p[0] = [p[1]] + p[3]
    elif len(p) == 2:
        p[0] = [p[1]]
    else:
        p[0] = []

def p_expression_tuple(p):
    "expression : '<' expression tuple_rest"
    p[0] = ('tuple', [p[2]] + p[3])

def p_tuple_rest(p):
    """tuple_rest : ',' expression tuple_rest
                  | '>'"""
    if len(p) == 4:
        p[0] = [p[2]] + p[3]
    else:
        p[0] = []

def p_expression_group(p):
    "expression : '(' expression ')'"
    p[0] = p[2]

def p_expression_lvalue(p):
    "expression : lvalue"
    p[0] = p[1]

def p_expression_call(p):
    "expression : methoddecl_or_call"
    p[0] = p[1]

def p_expression_number(p):
    "expression : NUMBER"
    p[0] = ('int', p[1])

def p_lvalue(p):
    """lvalue : IDENT
              | expression '.' IDENT lvalue_trailer
              | expression '[' expression ']' lvalue_trailer"""
    if len(p) == 2:
        p[0] = ('var', p[1])
    elif p[2] == ".":
        p[0] = ('lvalue', p[1], ('prop', p[3], p[4]))
    else:
        p[0] = ('lvalue', p[1], ('idx', p[3], p[5]))

def p_lvalue_trailer(p):
    """lvalue_trailer : '.' IDENT lvalue_trailer
                      | '[' expression ']' lvalue_trailer
                      | '(' arglist ')' lvalue_trailer
                      | """
    if len(p) == 1:
        p[0] = None
    elif p[1] == ".":
        p[0] = ('prop', p[2], p[3])
    elif p[1] == "[":
        p[0] = ('idx', p[2], p[4])
    elif p[1] == "(":
        p[0] = ('call', p[2], p[4])
    else:
        assert False

def p_methoddecl_or_call(p):
    """methoddecl_or_call : IDENT '(' arglist ')'"""
    p[0] = ('call', p[1], p[3])

def p_expression_new(p):
    "expression : new_alloc"
    p[0] = p[1]

def p_expression_method(p):
    "expression : method"
    p[0] = p[1]

def p_new(p):
    """new_alloc : NEW '(' locallist ')' '{' expression_list '}'"""
    p[0] = ('new', p[3], p[6])

def p_locallist(p):
    """locallist : local ',' locallist
                 | local
                 | """
    if len(p) == 4:
        p[0] = [p[1]] + p[3]
    elif len(p) == 2:
        p[0] = [p[1]]
    else:
        p[0] = []

def p_local(p):
    """local : IDENT '=' expression
             | IDENT """
    if len(p) == 4:
        p[0] = ('local', p[1], p[3])
    else:
        p[0] = ('local', p[1], None)

def p_method(p):
    """method : methoddecl_or_call '{' expression_list '}'"""
    assert p[1][0] == 'call'
    p[0] = ('method', p[1][1], p[1][2], p[3])

def p_expression_ite(p):
    """expression : IF expression '{' expression_list '}'
                  | IF expression '{' expression_list '}' ELSE '{' expression_list '}'"""
    if len(p) == 6:
        p[0] = ('ite', p[2], p[4], [])
    else:
        p[0] = ('ite', p[2], p[4], p[8])

def p_error(p):
    if p is None:
        raise Exception("Syntax error: unexpected EOF")
    else:
        col = find_column(p)
        line = p.lineno
        raise Exception("Syntax error (line {}, column {}): {}".format(line, col, p))


parser = yacc.yacc(tabmodule='parser_table')

# for testing
def parse_string(s):
    return parser.parse(s)


## ASTs #######################################################################


# Return an "AST" of type TopLevelNode
def string_to_ast(s):
    pt = parser.parse(s)
    assert isinstance(pt, tuple) and pt[0] == "toplevel"
    return parse_tree_to_ast(pt)


def parse_tree_to_ast(pt):
    if isinstance(pt, list):  # flatten a list into an ESeq
        if len(pt) == 0:
            return NopNode()
        exprs = list(map(parse_tree_to_ast, pt))
        e = exprs.pop()
        while exprs:
            e = SeqNode(exprs.pop(), e)
        return e
    elif pt[0] == 'toplevel':
        return TopLevelNode(list(map(parse_tree_to_ast, pt[1])))
    elif pt[0] == 'assign':
        lhs = parse_tree_to_ast(pt[1])
        rhs = parse_tree_to_ast(pt[2])
        return AssignNode(lhs, rhs)
    elif pt[0] == 'binop':
        lhs = parse_tree_to_ast(pt[2])
        rhs = parse_tree_to_ast(pt[3])
        return CallNode(ConstNil, pt[1], [lhs, rhs])
    elif pt[0] == 'unop':
        arg = parse_tree_to_ast(pt[2])
        isint = isinstance(arg, ConstNode) and isinstance(arg.val, IntNode)
        if isint and pt[1] == "-":
            return ConstNode(IntNode(-arg.val.val))
        elif isint and pt[1] == "+":
            return arg
        else:
            return CallNode(ConstNil, pt[1], [arg])
    elif pt[0] == 'tuple':
        return TupleNode(list(map(parse_tree_to_ast, pt[1])))
    elif pt[0] == 'int':
        return ConstNode(IntNode(pt[1]))
    elif pt[0] == 'var':
        return VarNode(pt[1])
    elif pt[0] == 'formal':
        return VarNode(pt[1], pt[2])
    elif pt[0] == 'call':
        return CallNode(ConstNil, pt[1], list(map(parse_tree_to_ast, pt[2])))
    elif pt[0] == 'lvalue':  # lvalue : IDENT trailer
        # this case is tricky: we need to reverse the parsing precedence,
        # which binds the first trailer first, whereas we want the first
        # trailer deepest in the AST.
        base = parse_tree_to_ast(pt[1])
        trailer = pt[2]
        while trailer is not None:
            if trailer[0] == 'prop':
                base = CompoundVarNode(base, trailer[1], ConstNil)
            elif trailer[0] == 'idx':
                idx = parse_tree_to_ast(trailer[1])
                if isinstance(base, CompoundVarNode) and base.idx is ConstNil:
                    base = CompoundVarNode(base.obj, base.name, idx)
                elif isinstance(base, CompoundVarNode):
                    raise Exception("don't know how to deal with multiple indexes")
                else:
                    base = CompoundVarNode(ConstNil, base.name, idx)
            elif trailer[0] == 'call':
                args = list(map(parse_tree_to_ast, trailer[1]))
                if isinstance(base, CompoundVarNode) and base.idx is ConstNil:
                    base = CallNode(base.obj, base.name, args)
                elif isinstance(base, CompoundVarNode):
                    raise Exception("don't know how to call on a compound var")
                else:
                    base = CallNode(ConstNil, base.name, args)
            trailer = trailer[2]
        return base
    elif pt[0] == 'new':
        lcls = list(map(parse_tree_to_ast, pt[1]))
        body = parse_tree_to_ast(pt[2])
        return NewNode(lcls, body)
    elif pt[0] == 'local':
        if pt[2] is None:
            return InitNode(pt[1], ConstNil)
        else:
            return InitNode(pt[1], parse_tree_to_ast(pt[2]))
    elif pt[0] == 'method':
        body = parse_tree_to_ast(pt[3])
        formals = list(map(parse_tree_to_ast, pt[2]))
        for a in formals:
            if not isinstance(a, VarNode):
                raise Exception("invalid method argument declaration", a)
        return MethodNode(pt[1], formals, body)
    elif pt[0] == 'ite':
        cnd = parse_tree_to_ast(pt[1])
        thn = parse_tree_to_ast(pt[2])
        els = parse_tree_to_ast(pt[3])
        return ITENode(cnd, thn, els)
    elif pt[0] == 'proof':
        proof_terms = lambda pr: parse_tree_to_ast(pr[0])
        proof_steps = lambda pr: parse_tree_to_ast(pr[1]) if pr[1] is not None else None
        proof_verbatims = lambda pr: pr[2]
        return ProofNode(list(map(proof_terms, pt[1])), list(map(proof_steps, pt[1])), list(map(proof_verbatims, pt[1])))
    elif pt[0] == 'proof-call':
        return CallNode(ConstNil, pt[1], list(map(parse_tree_to_ast, pt[2])))
    elif pt[0] == 'assert':
        return AssertNode(parse_tree_to_ast(pt[1]))
    elif pt[0] == 'assume':
        return AssumeNode(parse_tree_to_ast(pt[1]))
    else:
        raise Exception("unexpected parse tree node: {}".format(pt))
