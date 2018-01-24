import z3
## See https://en.wikipedia.org/wiki/Verbal_arithmetic
## cute: http://mathforum.org/library/drmath/view/60417.html

vars = dict()
def _mk_int_var (x):
    if x not in vars:
        vars[x] = z3.Int (str(x))
    return vars[x]

def mk_var (x):
    return _mk_int_var (x)

def get_vars ():
    return vars.values ()


def solve (s1, s2, s3):
    global vars
    vars = dict()

    # Replace with your solution
    pass


def print_sum (s1, s2, s3):
    s1 = str(s1)
    s2 = str(s2)
    s3 = str(s3)
    print s1.rjust (len(s3) + 1)
    print '+'
    print s2.rjust (len(s3) + 1)
    print ' ' + ('-'*(len(s3)))
    print s3.rjust (len(s3) + 1)
    
def puzzle (s1, s2, s3):
    print_sum (s1, s2, s3)
    res = solve (s1, s2, s3)
    if res is None:
        print 'No solution'
    else:
        print 'Solution:'
        print_sum (res[0], res[1], res[2])
        
if __name__ == '__main__':
    puzzle ('SEND', 'MORE', 'MONEY')
