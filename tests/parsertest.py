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


import os
import sys
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '../src')))

from frontend.parser import *


def test(s):
    print("=== " + s)
    print(parse_string(s))
    print(string_to_ast(s))

# print lex_string("5+6")
# print lex_string("5-(6*7)")

test("5+6")
test("5-(6*7)")
test("5-6*7")
test("x = 6")
test("x == 6")
print("")

test("5+6 7+8")
test("x=6 7==8")
test("5+6+7+8 x=6 7+9")
test("5+6+7+8; x=6; 7+9")
print("")

test("-6")
print("")

test("x = x + 1")
print("")

test("x[0]")
test("x.f")
test("x.f[0]")
test("x.f = 5")
test("x[0] = 5")
test("x.f[0] = 6")
test("x.f[0] = -6")
test("x.f[0] = x-6")
print("")

test("foo()")
test("foo(x)")
test("foo(x.t)")
test("x.foo()")
test("x.foo(x)")
test("x.foo(x.t)")
test("x.foo(x.t,y.p[0])")
print("")

test("foo.bar.baz")
# test("foo.bar.baz[0][1](x)(y)")
test("foo.bar[0]")
print("")

test("new(){}")
test("new(x=0){}")
test("new(x=0,y=v.x){}")
test("new(){foo(){}}")
test("new(x=0){foo(x){x}}")
test("new(x=0,y=v.x){foo(x,y){x=y}}")
print("")

test("if x { 6 }")
test("if x { 6 } else { 7 }")
test("if x.y[0] { new(x=0){} } else { new(y=0){} }")
print("")

test("new(xxx){get() {xxx}}")
test("x = new(x=0) { foo(y) { x = (x + y) }; bar() { x } }; x.foo(3); x.foo(6); x.bar()")

test("PrfC() { new () {} }")
test("PrfC() { new () {} }; PrfC()")
test("new(){foo(x,y){x=y 5 6 7}} 5 6 7")
test("PrfC(x) { new () { foo() { x } } }; x = PrfC(5); x.foo()")


test("""
FooA() { 
    new (x=1) { 
        bar(z) { 
            x 
        } 
    } 
}
FooB(x) {
    new () {
        bar(z) {
            x 
        }
    }
}
FooA() ~ FooB(1)
""")

test("new() { foo() { x y } }")

test("""
new() {}
// foobar
new() {}
""")

test("""
// outer comment
new() {
    // within an object body
    foo(x) {
        // within a method body 
        x
    }
}""")