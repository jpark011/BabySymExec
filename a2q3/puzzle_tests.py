import unittest
from a2q3.verbal_arithmetic import solve

class PuzzleTests (unittest.TestCase):

    def setUp (self):
        """Reset Z3 context between tests"""
        import z3
        z3._main_ctx = None
    def tearDown (self):
        """Reset Z3 context after test"""
        import z3
        z3._main_ctx = None

    def test_0 (self):
        """BASE CASE"""
        res = solve ('SEND', '', 'SEND')
        self.assertEquals (res, (9210, 0, 9210))

    def test_1 (self):
        """SEND + MORE = MONEY"""
        res = solve ('SEND', 'MORE', 'MONEY')
        self.assertEquals (res, (9567, 1085, 10652))

    def test_2 (self):
        """When s3 is shorter!! invalid"""
        res = solve ('SEND', 'MORE', 'CAT')
        self.assertEquals (res, None)

    def test_3 (self):
        """Unsat solution"""
        res = solve ('AAAA', 'BBBB', 'ABCDE')
        self.assertEquals (res, None)

    def test_4 (self):
        """When s3 is too long!"""
        res = solve ('SEND', 'MORE', 'CMONEY')
        self.assertEquals (res, None)
