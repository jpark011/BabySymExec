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
        
    def test_1 (self):
        """SEND + MORE = MONEY"""
        res = solve ('SEND', 'MORE', 'MONEY')
        self.assertEquals (res, (9567, 1085, 10652))

    def test_2 (self):
        pass

    def test_3 (self):
        pass
    
    def test_4 (self):
        pass
        
