# The MIT License (MIT)
# Copyright (c) 2016 Arie Gurfinkel

# Permission is hereby granted, free of charge, to any person obtaining
# a copy of this software and associated documentation files (the
# "Software"), to deal in the Software without restriction, including
# without limitation the rights to use, copy, modify, merge, publish,
# distribute, sublicense, and/or sell copies of the Software, and to
# permit persons to whom the Software is furnished to do so, subject to
# the following conditions:

# The above copyright notice and this permission notice shall be
# included in all copies or substantial portions of the Software.

# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
# EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
# MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
# NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
# LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
# OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
# WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

import unittest
import wlang.ast as ast
import wlang.sym

class TestSym (unittest.TestCase):
    def test_00 (self):
        prg1 = "x := 10; print_state"
        ast1 = ast.parse_string (prg1)
        sym = wlang.sym.SymExec ()
        st = wlang.sym.SymState ()
        out = [s for s in sym.run (ast1, st)]
        self.assertEquals (len(out), 1)

    def test_01 (self):
        prg1 = "havoc x; assume x > 10"
        ast1 = ast.parse_string (prg1)
        sym = wlang.sym.SymExec ()
        st = wlang.sym.SymState ()
        out = [s for s in sym.run (ast1, st)]
        self.assertEquals (len(out), 1)

    def test_02 (self):
        prg1 = "x := 10; y := 11; z := x + y; assert z = x + y"
        ast1 = ast.parse_string (prg1)
        sym = wlang.sym.SymExec ()
        st = wlang.sym.SymState ()
        out = [s for s in sym.run (ast1, st)]
        self.assertEquals (len(out), 1)

    def test_03 (self):
        prg1 = """
            havoc x, y;
            z := x + y;
            if x > y then
              z := x
            else
              z := y
        """
        ast1 = ast.parse_string (prg1)
        sym = wlang.sym.SymExec ()
        st = wlang.sym.SymState ()
        out = [s for s in sym.run (ast1, st)]
        self.assertEquals (len(out), 2)

    def test_04 (self):
        prg1 = """
            x:=0;
            y:=0;
            z:=0;
            havoc a, b, c;

            if not a = 0 then {
              x := -2
            };

            if b < 5 then {
              if a = 0 and not(c = 0) then
                y := 1;
              z := 2
            }
        """
        ast1 = ast.parse_string (prg1)
        sym = wlang.sym.SymExec ()
        st = wlang.sym.SymState ()
        out = [s for s in sym.run (ast1, st)]
        self.assertEquals (len(out), 5)

    def test_05 (self):
        prg1 = """
            x := 10;
            y := 5;
              while x > 0
              do {
                if x > y then
                  x := x-1
              }
        """
        ast1 = ast.parse_string (prg1)
        sym = wlang.sym.SymExec ()
        st = wlang.sym.SymState ()
        out = [s for s in sym.run (ast1, st)]
        self.assertEquals (len(out), 1)

    def test_06 (self):
        prg1 = """
            x := (1 + 2) / 3 - 3 * 5;
            skip
        """
        ast1 = ast.parse_string (prg1)
        sym = wlang.sym.SymExec ()
        st = wlang.sym.SymState ()
        out = [s for s in sym.run (ast1, st)]
        self.assertEquals (len(out), 1)

    def test_07 (self):
        prg1 = """
            havoc x, y;
            if x >= y or x <= y then
              z := x
            else
              z := y;

            if true or x > y then
                 z := x
               else
                 z := y
        """
        ast1 = ast.parse_string (prg1)
        sym = wlang.sym.SymExec ()
        st = wlang.sym.SymState ()
        out = [s for s in sym.run (ast1, st)]
        self.assertEquals (len(out), 1)
