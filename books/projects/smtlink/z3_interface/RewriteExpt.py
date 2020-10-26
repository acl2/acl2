# Copyright (C) 2015, University of British Columbia
# Written (originally) by Mark Greenstreet (13th March, 2014)
# Edited by Yan Peng (11th Nov. 2016)
#
# License: A 3-clause BSD license.
# See the LICENSE file distributed with ACL2

import collections
import ACL2_to_Z3
import z3
from functools import reduce # for Python 2/3 compatibility

def prod(stuff):
    """ prod(stuff):
            compute the product (i.e. reduce with '*') of the elements of 'stuff'.
            'stuff' must be iterable."""
    return reduce(lambda x, y: x*y, stuff)

def longVal(x):
    """ longVal(x):
          if 'x' is a z3 constant (i.e. function of arity 0) whose value is an integer,
            then return that integer as a python long
            else return 'None'"""
    if(hasattr(x, 'as_long')): return x.as_long()
    elif(hasattr(x, 'numerator_as_long')):
        if(x.denominator_as_long() == 1): return x.numerator_as_long()
    return None
# end longVal

class to_smt_w_expt(ACL2_to_Z3.ACL22SMT):
    class ExptRewriteFailure(Exception): pass

    def __init__(self, *args):
        super(to_smt_w_expt, self).__init__(*args)
        # I'm making the exponent have sort Real instead of Int because
        # the translator turns integerp to isReal!  That's because the z3
        # solver (understandably) chokes on mixed integer/real polynomials.
        self.expt = z3.Function('EXPT-RATIONALP', z3.RealSort(), z3.RealSort(), z3.RealSort())
        # self.b_sum = z3.Function('b_sum', z3.RealSort(), z3.RealSort(), z3.RealSort(), z3.RealSort(), z3.RealSort(), z3.RealSort(), z3.RealSort())
        # self.b_expt = z3.Function('b_expt', z3.RealSort(), z3.RealSort(), z3.RealSort())
        self.maxPowExpand = 10

    def simplify(self, expr, **kwargs):
        if(z3.is_expr(expr)): return z3.simplify(expr, **kwargs)
        else: # assume that expr has already been 'simplified' to a constant.
          return expr

    def reportFun(self, report=None):
        def print_msg(*args):
            print(''.join([str(a) for a in args]))
            return None
        def dont_print_msg(*args):
            return None
        if((report is None) or (report is False)): return dont_print_msg
        elif(report is True): return print_msg
        else: return report

    def get_expt_rules(self, expr_list, report=None):
        if(len(expr_list) == 0): return []
        else: hyps = expr_list[0]
        workQ = collections.deque()  # expt calls we still need to examine
        allQ = collections.deque()   # all expt calls that we've seen
        report = self.reportFun(report)

        def enqueue(v):
            # z3 ASTs are unhashable; so we'll use a brute-force
            #   list for now -- beware of the quadratic time to build the
            #   allQ and workQ lists if we ever work on big examples.
            report('enque(', v, ')')
            for w in allQ:
                if(v.eq(w)):  # have we already seen v ?
                    report('  already seen, no work to do')
                    return
            report('  appending ', v, ' to allQ and workQ')
            allQ.append(v)
            workQ.append(v)

        def xpt(x, n):
            v = self.expt(x, n)
            enqueue(v)
            return v

        def lookfor_expt(v):
            if(v is None): return
            elif(hasattr(v, "decl") and hasattr(v, "children")):
              # hopefully, v is a z3 expression
              if(v.decl().eq(self.expt)):
                  x = v.children()[0]
                  n = v.children()[1]
                  enqueue(self.expt(x, self.simplify(n, som=True)))
              for nu in v.children(): lookfor_expt(nu)

        def expt_rules():
            rules = collections.deque()
            solver = z3.Solver()
            solver.set('arith.nl', False)
            solver.add(hyps)

            def show(p):
                report('trying to show(', p, '):')
                report('  hypotheses = ', solver)
                solver.push()
                solver.add(z3.Not(p))
                outcome = solver.check()
                s1 = '  the negation is ' + str(outcome)
                if(outcome == z3.unsat):
                  report(s1, "; therefore the original claim is valid")
                elif(outcome == z3.sat):
                  report(s1, "\n  here's a counter-example to ", p, "\n  ", solver.model())
                elif(outcome == z3.unknown):
                  report(s1, "; therefore, the original claim is undecided")
                else:
                  report(s1, "; how'd that happen?")
                solver.pop()
                return outcome == z3.unsat

            def add_rule(p):
                report('add_rule(', p, ')')
                rules.append(p)
                solver.add(p)

            while(len(workQ) > 0):
                v = workQ.pop()
                x = v.children()[0]
                n = v.children()[1]

                report('rewriting expt(', x, ', ', n, ')')

                # Many of the rules below should have guards to ensure that we don't
                # accidentally say expt(x, n) is defined when x==0 and n < 0.
                # Rather that figuring out # all of the corner cases, I first check to
                # see if (x == 0) and (n < 0) is satisfiable.  If so, this code just
                # throws an exception.  I could probably work out a better error message
                # later.
                #   Now that we know that expt(x, n) is well-defined, we still need to be careful.
                # Consider expt(x, n+m) where x==0, n==3, and m==(-2).  In this case, expt(x, n+m)
                # is well-defined, but we can't conclude:
                #    expt(x, n+m) == expt(x, n) * expt(x, m)
                # Rather than working out lots of side conditions (and probably making a mistake),
                # I just check to see if implies(hyps, x > 0), and then plunge ahead without fear.
                # Of course, this means I don't generate all of the rules that I could, but I'll
                # do that later if this simple version turns out to be useful.

                def expt_rewrite_const(x2, n2):
                    if(n2 == 0): return z3.intVal(1)
                    elif((0 < n2) and (n2 <= self.maxPowExpand)):
                        add_rule(v == prod(map(lambda _: x2, range(n2))))
                    elif((-self.maxPowExpand <= n2) and (n2 < 0)):
                        add_rule(v*prod(map(lambda _: x2, range(-n2))) == 1)
                if(not show(z3.Or(x != 0, n >= 0))):
                    raise ExptRewriteFailure('possible attempt to raise 0 to a negative power')

                x_is_pos = show(x > 0)
                x_is_nz  = x_is_pos or show(x != 0)
                x_is_z   = (not x_is_nz) and show(x == 0)

                n_is_pos = show(n > 0)
                n_is_neg = (not n_is_pos) and show(n < 0)
                n_is_z   = (not n_is_pos) and (not n_is_neg) and show(n == 0)

                if(n_is_z or x_is_z):
                    if(n_is_z): add_rule(v == 1)
                    elif(n_is_pos): add_rule(v == 0)
                    else: add_rule(v == z3.If(n == 0, 1, 0))
                    continue
                elif(x_is_pos):
                    x_lt_1 = show(x < 1)
                    x_gt_1 = (not x_lt_1) and show(x > 1)
                    if((not x_lt_1) and (not x_gt_1) and show(x == 1)):
                        add_rule(v == 1)
                        continue
                    add_rule(v > 0)
                else:
                  add_rule(z3.Implies(x > 0, v > 0))
                  if(x_is_nz): add_rule(z != 0)
                  else: add_rule(z3.Implies(z3.Or(x != 0, n==0), v != 0))

                if((x.decl().name() == '*') and (len(x.children()) > 1)): # expt(x0*x1*..., n)
                    add_rule(v == prod(map(lambda y: xpt(y, n), x.children())))
                elif((n.decl().name() == '+') and (len(n.children()) > 1)): # expt(x, n0+n1+...)
                    add_rule(v == prod(map(lambda m: xpt(x, m), n.children())))
                elif(n.decl().name() == '-'):
                    nn = n.children()
                    if(len(nn) == 0): pass  # a variable named '-'
                    elif(len(nn) == 1): # expt(x, -n)
                        add_rule(z3.Implies(x != 0, v*xpt(x, nn[0]) == 1))
                    elif(len(nn) == 2): # expt(x, n-m)
                        add_rule(z3.Implies(x != 0, v*xpt(x, nn[1]) == xpt(x, nn[0])))
                    else: RewriteExptFailure("unexpected: '-' expression with more than two children")
                elif(n.decl().name() == '*'):  # expt(x, n0*n1*...)
                    # check to see if n0 is integer constants and not "too big".
                    # if so, replace it with repeated multiplication
                    nn = n.children()
                    if((len(nn) > 0) and not (longVal(nn[0]) is None)):
                        if(len(nn) == 1): ex = x
                        else: ex = xpt(x, prod(nn[1:]))
                        expt_rewrite_const(ex, longVal(nn[0]))
                elif(not (longVal(n) is None)):
                    expt_rewrite_const(x, longVal(n))
                else: # we can't think of a way to simplify it
                    if(x_lt_1 or x_gt_1):
                        if(n_is_pos or n_is_neg): pass
                        else: add_rule(z3.Implies(n == 0, v == 1))
                    else:
                        if(n_is_pos or n_is_neg): add_rule(z3.Implies(x==1, v == 1))
                        else: add_rule(z3.Implies(z3.Or(x==1, n == 0), v == 1))
                    if(x_is_pos):
                        if(x_lt_1):
                            if(n_is_pos): add_rule(v <= x)
                            elif(n_is_neg): add_rule(v*x >= 1)
                            else: add_rule(z3.And(
                                z3.Implies(n > 0, v <= x),
                                z3.Implies(n < 0, v*x >= 1)))
                        elif(x_gt_1):
                            if(n_is_pos): add_rule(v >= x)
                            elif(n_is_neg): add_rule(v*x <= 1)
                            else: add_rule(z3.And(
                                z3.Implies(n > 0, v >= x),
                                z3.Implies(n < 0, v*x <= 1)))
                        else: add_rule(z3.And(
                            z3.Implies(z3.And(x < 1, n > 0), v <= x),
                            z3.Implies(z3.And(x < 1, n < 0), v*x >= 1),
                            z3.Implies(z3.And(x > 1, n > 0), v >= x),
                            z3.Implies(z3.And(x > 1, n < 0), v*x <= 1)))
            return rules
        # end expt_rules

        for x in expr_list: lookfor_expt(x)
        return expt_rules()

    # using z3's If function is simpler, and probably more efficient
    #   than introducing a new variable as is done in ACL2_translator
    def ifx(self, condx, thenx, elsex):
      return z3.If(condx, thenx, elsex)

    # The ACL2 code should access Q as a method of the to_smt object and not
    # as a separate method.  I'm creating the method here so this will work
    # right when the ACL2 code is modified.  OTOH, ACL2_translator will probably
    # get updated as well, in which case this methods will be redundant
    def Q(self, numerator, denominator): return z3.Q(numerator, denominator)

    def analyse_expt(self, hypotheses, conclusion=None, report=None):
        report = self.reportFun(report)
        expt_hyps = self.get_expt_rules([hypotheses, conclusion], report)
        # expt_hyps = []
        if(len(expt_hyps) == 0):
            hyps = hypotheses
            concl = conclusion
        elif(conclusion is None):
            hyps = z3.And(*expt_hyps)
            concl = hypotheses
        else:
            hyps = z3.And(hypotheses, *expt_hyps)
            concl = conclusion
        simple_hyps  = self.simplify(hyps)
        simple_concl = self.simplify(concl)
        return simple_hyps, simple_concl

    # is x uninterpreted function instance
    def is_uninterpreted_fun(self, x):
        d = x.decl()
        return(
            all([hasattr(d, a) for a in ('__call__', 'arity', 'domain', 'kind', 'range')]) and
            (d.kind() == z3.Z3_OP_UNINTERPRETED) and
            d.arity() > 0)

    # I'll assume that all arguments are z3 expressions except for possibly the
    # last one.  If the last one is a function, then it's the 'report' function
    # for debugging.
    def fun_to_var(self, exprs, report=None):
        report = self.reportFun(report)
        report('fun_to_var(', exprs, ', ', report, ')')

        funQ = collections.deque()  # uninterpreted functions we've seen

        def helper(x):
            if(x is None):
                return x
            elif(self.is_uninterpreted_fun(x)):
                match = [f[1] for f in funQ if f[0] is x]
                if(len(match) == 1):  # found a match
                    return match[0]
                else:
                    rangeSort = x.decl().range()
                    varName = '|$' + str(x) + '|'
                    if(rangeSort == z3.RealSort()): newVar = z3.Real(varName)
                    elif(rangeSort == z3.IntSort()): newVar = z3.Int(varName)
                    elif(rangeSort == z3.BoolSort()): newVar = z3.Bool(varName)
                    else:
                        raise ExptRewriteFailure(
                            'unknown sort for range of uninterpreted function -- ' +
                            varName + ' returns a ' + rangeSort + ' ?')
                    funQ.append((x, newVar))
                    return newVar
            else:
                ch = x.children()
                newch = self.fun_to_var(ch, report)
                if(len(ch) != len(newch)):
                    raise ExptRewriteFailure('Internal error')
                elif(len(newch) == x.decl().arity()):
                    return x.decl().__call__(*newch)
                elif((x.decl().arity() == 2) and (len(newch) > 2)):
                    return reduce(x.decl(), newch)
                else:
                    raise ExptRewriteFailure('Internal error')

        newExprs = [helper(x) for x in exprs]
        report('fun_to_var(', exprs, ') -> ', newExprs)
        return newExprs

    def prove(self, hypotheses, conclusion=None, report=None):
        report = self.reportFun(report)

        if (conclusion is None):
            conclusion = hypotheses
            hypotheses = True

        x_hyps, x_concl = self.analyse_expt(z3.And(hypotheses,z3.Not(conclusion)), conclusion, report)
        f_hyps, f_concl = self.fun_to_var([x_hyps, x_concl], report)[:]
        if(f_hyps is None):
            hyps = f_hyps
        else:
            hyps = z3.simplify(f_hyps)
        if(f_concl is None):
            concl = f_concl
        else:
            concl = z3.simplify(f_concl)

        report('to_smt_w_expt.prove:')
        report('  hypotheses = ', hyps)
        report('  conclusion = ', concl)
        return super(to_smt_w_expt, self).prove(hyps, concl)
