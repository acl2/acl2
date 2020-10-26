# Copyright (C) 2015, University of British Columbia
# Written (originally) by Mark Greenstreet (13th March, 2014)
# Counter-example generation: Carl Kwan (May 2016)
# Edited by Yan Peng (15th Nov 2016)
#
# License: A 3-clause BSD license.
# See the LICENSE file distributed with ACL2
import re
from z3 import *
from functools import reduce # for Python 2/3 compatibility

def sort(x):
    if type(x) == bool:    return BoolSort()
    elif type(x) == int:   return IntSort()
    elif type(x) == float: return RealSort()
    elif hasattr(x, 'sort'):
        if x.sort() == BoolSort(): return BoolSort()
        if x.sort() == IntSort():  return IntSort()
        if x.sort() == RealSort(): return RealSort()
        else:
            raise Exception('unknown sort for expression')

class ACL22SMT(object):

    class Symbol:
        # define the Z3Sym type
        z3Sym = Datatype('Symbol')
        z3Sym.declare('sym', ('ival', IntSort()))
        z3Sym = z3Sym.create()

        # operations for creating a dictionary of symbols
        count = 0
        dict = {}

        def intern(self, name):
            try: return(self.dict[name])
            except:
                self.dict[name] = self.z3Sym.sym(self.count)
                self.count = self.count + 1
                return(self.dict[name])

        def interns(self, namelist):
            return [ self.intern(name) for name in namelist ]

    class status:
        def __init__(self, value):
            self.value = value

        def __str__(self):
            if(self.value is True): return 'QED'
            elif(self.value.__class__ == 'msg'.__class__): return self.value
            else: raise Exception('unknown status?')

        def isThm(self):
            return(self.value is True)

    class atom:  # added my mrg, 21 May 2015
        def __init__(self, string):
            self.who_am_i = string.lower()
        def __eq__(self, other):
            return(self.who_am_i == other.who_am_i)
        def __ne__(self, other):
            return(self.who_am_i != other.who_am_i)
        def __str__(self):
            return(self.who_am_i)

    def __init__(self, solver=None):
        if(solver != None): self.solver = solver
        else: self.solver = Solver()
        self.nameNumber = 0

    # ---------------------------------------------------------
    #                   Basic Functions
    #

    # Type declarations
    def IntSort(self): return IntSort()
    def RealSort(self): return RealSort()
    def BoolSort(self): return BoolSort()
    # type related functions
    def integerp(self, x): return sort(x) == IntSort()
    def rationalp(self, x): return sort(x) == RealSort()
    def booleanp(self, x): return sort(x) == BoolSort()

    # manually casting integer sort to real sort
    def to_real(self, x):
        if(hasattr(x, 'sort') and x.sort() == IntSort()):
            return(ToReal(x))
        else:
            return(x)

    def plus(self, *args): return reduce(lambda x, y: x+y, args)
    def times(self, *args): return reduce(lambda x, y: x*y, args)

    def reciprocal(self, x):
        if(type(x) is int): return(Q(1,x))
        elif(type(x) is float): return 1.0/x
        # Casting variable of IntSort to real
        else: return 1.0/self.to_real(x)

    def negate(self, x): return -x
    def lt(self, x,y): return self.to_real(x) < self.to_real(y)
    def equal(self, x,y): return self.to_real(x) == self.to_real(y)
    def notx(self, x): return Not(x)
    def implies(self, x, y): return Implies(x,y)
    def Qx(self, x, y): return Q(x,y)

    def ifx(self, condx, thenx, elsex):
        try:
            return If(condx, thenx, elsex)
        except:
            print('If failed')
            print('If(' + str(condx) + ', ' + str(thenx) + ', ' + str(elsex) + ')')
            raise Exception('giving up')

    # def hint_okay(self):
    #     return False

    # # -------------------------------------------------------------
    # #       Replacing uninterpreted functions with free vars
    # fun2var_count = 0
    # funQ = dict()  # uninterpreted functions we've seen

    # def next_fresh_var(self):
    #     count = self.fun2var_count
    #     self.fun2var_count = self.fun2var_count+1
    #     return count

    # def reportFun(self, report=None):
    #     def print_msg(*args):
    #         print(''.join([str(a) for a in args]))
    #         return None
    #     def dont_print_msg(*args):
    #         return None
    #     if((report is None) or (report is False)): return dont_print_msg
    #     elif(report is True): return print_msg
    #     else: return report

    # # is x uninterpreted function instance
    # def is_uninterpreted_fun(self, x):
    #     d = x.decl()
    #     return(
    #         all([hasattr(d, a) for a in ('__call__', 'arity', 'domain', 'kind', 'range')]) and
    #         (d.kind() == z3.Z3_OP_UNINTERPRETED) and
    #         d.arity() > 0)

    # # I'll assume that all arguments are z3 expressions except for possibly the
    # # last one.  If the last one is a function, then it's the 'report' function
    # # for debugging.
    # def fun_to_var(self, exprs, report=None):
    #     report = self.reportFun(report)
    #     report('fun_to_var(', exprs, ', ', report, ')')

    #     def helper(x):
    #         if(x is None):
    #             return x
    #         elif(self.is_uninterpreted_fun(x)):
    #             if(x in self.funQ):  # found a match
    #                 return self.funQ[x]
    #             else:
    #                 rangeSort = x.decl().range()
    #                 varName = 'SMT_fun2var_' + str(self.next_fresh_var())
    #                 newVar = z3.Const(varName, rangeSort)
    #                 self.funQ[x] = newVar
    #                 return newVar
    #         else:
    #             ch = x.children()
    #             newch = self.fun_to_var(ch, report)
    #             if(len(ch) != len(newch)):
    #                 raise Exception('Internal error')
    #             elif(len(newch) == x.decl().arity()):
    #                 return x.decl().__call__(*newch)
    #             elif((x.decl().arity() == 2) and (len(newch) > 2)):
    #                 return reduce(x.decl(), newch)
    #             else:
    #                 raise Exception('Internal error')

    #     newExprs = [helper(x) for x in exprs]
    #     report('fun_to_var(', exprs, ') -> ', newExprs)
    #     return newExprs

    # -------------------------------------------------------------
    #       Proof functions and counter-example generation

    def get_vars(self, asserts):
        """
        Return a list of ArithRef objects of variables appeared
        in the list of expressions stored in asserts.
        """
        acc = []

        def get_vars_ast(v):
            if(hasattr(v, "children")):
                # hopefully, v is a z3 expression
                if v.children() == []:
                    if not(is_int_value(v) or \
                           is_rational_value(v) or \
                           is_true(v) or is_false(v) or \
                           v.sexpr() == 'nil'):
                        return [v]
                    else:
                        return []
                else:
                    children_lst = []
                    for nu in v.children():
                        children_lst += get_vars_ast(nu)
                    return children_lst
            else:
                return []

        for ast in asserts:
            acc += get_vars_ast(ast)

        return list(set(acc))


    def get_model(self, var_lst):
        m = self.solver.model()
        dontcare_lst = []
        model_lst = []
        for var in var_lst:
            if m.__getitem__(var) == None:
                value = m.eval(var, model_completion = True)
                dontcare_lst.append([var, value])
            else:
                value = m.eval(var)
                model_lst.append([var, value])
        return [model_lst, dontcare_lst]


    def translate_to_acl2(self, model_lst, dontcare_lst):
        model_acl2 = []
        dontcare_acl2 = []

        def translate_value(n, v):
            translated_v = str(v)
            if (is_algebraic_value(v)):
                rt_obj = str(v.sexpr())
                rt_obj = rt_obj.replace("root-obj", "cex-root-obj " + n + " state")
                translated_v = rt_obj

            translated_v = translated_v.replace(",", "")
            translated_v = re.sub(r"([a-zA-Z0-9_]+?)\(", r"\(\1 ", translated_v)
            translated_v = translated_v.replace(".0", "").replace("False", "nil").replace("True","t")
            return translated_v

        def translate_model(model):
            m = model[0]
            name = m.decl().name()
            value = model[1]
            return "(" + name + " " + translate_value(name, value) + ")"

        model_acl2 = [translate_model(model) for model in model_lst]
        dontcare_acl2 = [translate_model(model) for model in dontcare_lst]
        return [model_acl2, dontcare_acl2]


    def proof_counterExample(self):
        asserts = self.solver.assertions()
        var_lst = self.get_vars(asserts)
        [model_lst, dontcare_lst] = self.get_model(var_lst)
        [model_acl2, dontcare_acl2] = self.translate_to_acl2(model_lst, dontcare_lst)

        print('\'(' + ' '.join(model_acl2+dontcare_acl2) + ')')
        print('Without dontcares: ' + '\'(' + ' '.join(model_acl2) + ')')

    def proof_success(self):
        print('proved')

    def proof_fail(self):
        print('failed to prove')

    # usage prove(claim) or prove(hypotheses, conclusion)
    def prove(self, hypotheses, conclusion=None):
        if(conclusion is None): claim = hypotheses
        else: claim = Implies(hypotheses, conclusion)

        # claim = self.fun_to_var([claim], False)[0]

        self.solver.push()
        self.solver.add(Not(claim))
        res = self.solver.check()

        if res == unsat: self.proof_success()
        elif res == sat: self.proof_counterExample()
        else: self.proof_fail()

        self.solver.pop()
        return(self.status(res == unsat))
