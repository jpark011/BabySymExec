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

def to_solution (s, model):
    if len(s) is 0:
        return 0
    ret = ""

    for c in s:
        ret += model[mk_var(c)].as_string()

    return int(ret)


def solve (s1, s2, s3):
    global vars
    vars = dict()

    # z3 setUp
    solver = z3.Solver()

    # get len
    s1_len = len(s1)
    s2_len = len(s2)
    s3_len = len(s3)

    # s3 should be longest
    solver.add(z3.IntVal(s1_len) <= z3.IntVal(s3_len))
    solver.add(z3.IntVal(s2_len) <= z3.IntVal(s3_len))

    # reverse all strings
    s1_r = s1[::-1]
    s2_r = s2[::-1]
    s3_r = s3[::-1]

    # iterate 0 to s3_len
    for i in range(s3_len):
        # set c1
        if i < s1_len:
            c1 = mk_var(s1_r[i])
        else:
            c1 = z3.IntVal(0)

        # set c1_prev
        if 0 < i and i <= s1_len:
            c1_prev = mk_var(s1_r[i-1])
        else:
            c1_prev = z3.IntVal(0)


        # set c2
        if i < s2_len:
            c2 = mk_var(s2_r[i])
        else:
            c2 = z3.IntVal(0)

        # set c2_prev
        if 0 < i and i <= s2_len:
            c2_prev = mk_var(s2_r[i-1])
        else:
            c2_prev = z3.IntVal(0)

        #set c3
        c3 = mk_var(s3_r[i])

        # assertion
        # first when it's the first ele
        solver.add(c3 == (c1 + c2 + (c1_prev + c2_prev) / 10) % 10)

    # make sure each var is single digit
    for v in get_vars():
        solver.add(0 <= v, v <= 9)

    # all solutions should be distinct
    solver.add(z3.Distinct(get_vars()))

    # solve
    res = solver.check()

    if res == z3.sat:
        model = solver.model()

        sol1 = to_solution(s1, model)
        sol2 = to_solution(s2, model)
        sol3 = to_solution(s3, model)

        return (sol1, sol2, sol3)
    else:
        return None

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
