; Former-Centaur Meta-reasoning Library
; Copyright (C) 2022 Intel Corporation
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Sol Swords <sol.swords@intel.com>


(in-package "CMR")

(include-book "clause-processors/pseudo-term-fty" :dir :System)
(include-book "centaur/misc/starlogic" :dir :system)
(local (include-book "clause-processors/join-thms" :dir :system))

(defevaluator flatten-ev flatten-ev-list
  ((not x)
   (if x y z)
   (implies x y))
  :namedp t)

(local (acl2::def-ev-pseudo-term-fty-support flatten-ev flatten-ev-list))
(local (acl2::def-join-thms flatten-ev))

(local (defthm pseudo-term-listp-of-append
         (implies (and (pseudo-term-listp x)
                       (pseudo-term-listp y))
                  (pseudo-term-listp (append x y)))))
        
(define dumb-negate ((x pseudo-termp))
  :returns (neg-x pseudo-termp)
  (pseudo-term-case x
    :fncall (if (eq x.fn 'not)
                (car x.args)
              `(not ,(pseudo-term-fix x)))
    :otherwise `(not ,(pseudo-term-fix x)))
  ///
  (defthm dumb-negate-correct
    (iff (flatten-ev (dumb-negate x) a)
         (not (flatten-ev x a)))))

(define dumb-conjunction-to-literals ((x pseudo-termp))
  :returns (lits pseudo-term-listp)
  :measure (pseudo-term-count x)
  (pseudo-term-case x
    :fncall (if (and (eq x.fn 'if)
                     (equal (third x.args) ''nil))
                (cons (dumb-negate (first x.args))
                      (dumb-conjunction-to-literals (second x.args)))
              (list (dumb-negate (pseudo-term-fix x))))
    :otherwise (list (dumb-negate (pseudo-term-fix x))))
  ///
  (defthm dumb-conjunction-to-literals-correct
    (iff (flatten-ev (disjoin (dumb-conjunction-to-literals x)) a)
         (not (flatten-ev x a)))))


(define dumb-formula-to-clause ((x pseudo-termp))
  :returns (clause pseudo-term-listp)
  (pseudo-term-case x
    :fncall (if (eq x.fn 'implies)
                (append (dumb-conjunction-to-literals (car x.args))
                        (list (cadr x.args)))
              (list (pseudo-term-fix x)))
    :otherwise (list (pseudo-term-fix x)))
  ///
  (defthm dumb-formula-to-clause-correct
    (iff (flatten-ev (disjoin (dumb-formula-to-clause x)) a)
         (flatten-ev x a))))

(define dumb-negate-each ((x pseudo-term-listp))
  :returns (neg-x pseudo-term-listp)
  (if (atom x)
      nil
    (cons (dumb-negate (car x))
          (dumb-negate-each (cdr x))))
  ///
  (defthm disjoin-of-dumb-negate-each
    (iff (flatten-ev (disjoin (dumb-negate-each x)) a)
         (not (flatten-ev (conjoin x) a))))
  (defthm conjoin-of-dumb-negate-each
    (iff (flatten-ev (conjoin (dumb-negate-each x)) a)
         (not (flatten-ev (disjoin x) a)))))

(defthm flatten-ev-of-disjoin-pseudo-term-list-fix
  (iff (flatten-ev (disjoin (pseudo-term-list-fix x)) a)
       (flatten-ev (disjoin x) a))
  :hints(("Goal" :induct (len x)
          :in-theory (enable pseudo-term-list-fix len))))

(define dumb-disjoin-lit-lists ((x pseudo-term-listp)
                                (y pseudo-term-listp))
  :returns (disj pseudo-term-listp)
  (b* ((x (pseudo-term-list-fix x))
       (y (pseudo-term-list-fix y)))
    (if (or (equal x '('t))
            (equal y '('t)))
        '('t)
      (append x y)))
  ///
  (defthm dumb-disjoin-lit-lists-correct
    (iff (flatten-ev (disjoin (dumb-disjoin-lit-lists x y)) a)
         (or (flatten-ev (disjoin x) a)
             (flatten-ev (disjoin y) a)))
    :hints (("goal" :use ((:instance flatten-ev-of-disjoin-pseudo-term-list-fix
                           (x x))
                          (:instance flatten-ev-of-disjoin-pseudo-term-list-fix
                           (x y)))
             :in-theory (disable flatten-ev-of-disjoin-pseudo-term-list-fix)))))



(defthm flatten-ev-of-conjoin-pseudo-term-list-fix
  (iff (flatten-ev (conjoin (pseudo-term-list-fix x)) a)
       (flatten-ev (conjoin x) a))
  :hints(("Goal" :induct (len x)
          :in-theory (enable pseudo-term-list-fix len))))

(define dumb-conjoin-lit-lists ((x pseudo-term-listp)
                                (y pseudo-term-listp))
  :returns (disj pseudo-term-listp)
  (b* ((x (pseudo-term-list-fix x))
       (y (pseudo-term-list-fix y)))
    (if (or (equal x '('nil))
            (equal y '('nil)))
        '('nil)
      (append x y)))
  ///
  (defthm dumb-conjoin-lit-lists-correct
    (iff (flatten-ev (conjoin (dumb-conjoin-lit-lists x y)) a)
         (and (flatten-ev (conjoin x) a)
              (flatten-ev (conjoin y) a)))
    :hints (("goal" :use ((:instance flatten-ev-of-conjoin-pseudo-term-list-fix
                           (x x))
                          (:instance flatten-ev-of-conjoin-pseudo-term-list-fix
                           (x y)))
             :in-theory (disable flatten-ev-of-conjoin-pseudo-term-list-fix)))))



(defines dumb-flatten-disjunction
  (define dumb-flatten-disjunction ((x pseudo-termp))
    :returns (lits pseudo-term-listp)
    :measure (pseudo-term-count x)
    (pseudo-term-case x
      :fncall (b* (((when (acl2::and** (eq x.fn 'not)
                                 (eql (len x.args) 1)))
                    (dumb-negate-each (dumb-flatten-conjunction (first x.args))))
                   ((when (acl2::and** (eq x.fn 'implies)
                                 (eql (len x.args) 2)))
                    (dumb-disjoin-lit-lists (dumb-negate-each (dumb-flatten-conjunction (first x.args)))
                                            (dumb-flatten-disjunction (second x.args))))
                   ((unless (acl2::and** (eq x.fn 'if)
                                   (eql (len x.args) 3)))
                    (list (pseudo-term-fix x)))
                   ((when (and (equal (second x.args) ''nil)
                               (equal (third x.args) ''t)))
                    (dumb-negate-each
                     (dumb-flatten-conjunction (first x.args))))
                   ((when (or (equal (first x.args) (second x.args))
                              (equal (second x.args) ''t)))
                    (dumb-disjoin-lit-lists (dumb-flatten-disjunction (first x.args))
                                            (dumb-flatten-disjunction (third x.args)))))
                (list (pseudo-term-fix x)))
      :const (if x.val
                 '('t)
               nil)
      :otherwise (list (pseudo-term-fix x))))

  (define dumb-flatten-conjunction ((x pseudo-termp))
    :returns (lits pseudo-term-listp)
    :measure (pseudo-term-count x)
    :verify-guards nil
    (pseudo-term-case x
      :fncall (b* (((when (acl2::and** (eq x.fn 'not)
                                 (eql (len x.args) 1)))
                    (dumb-negate-each (dumb-flatten-disjunction (first x.args))))
                   ((unless (acl2::and** (eq x.fn 'if)
                                   (eql (len x.args) 3)))
                    (list (pseudo-term-fix x)))
                   ((when (and (equal (second x.args) ''nil)
                               (equal (third x.args) ''t)))
                    (dumb-negate-each
                     (dumb-flatten-disjunction (first x.args))))
                   ((when (equal (third x.args) ''nil))
                    (dumb-conjoin-lit-lists (dumb-flatten-conjunction (first x.args))
                                            (dumb-flatten-conjunction (second x.args)))))
                (list (pseudo-term-fix x)))
      :const (if x.val
                 nil
               '('nil))
      :otherwise (list (pseudo-term-fix x))))
  ///
  (verify-guards dumb-flatten-disjunction)

  (defret-mutual dumb-flatten-disjunction-correct
    (defret dumb-flatten-disjunction-correct
      (iff (flatten-ev (disjoin (dumb-flatten-disjunction x)) a)
           (flatten-ev x a))
      :fn dumb-flatten-disjunction)
    (defret dumb-flatten-conjunction-correct
      (iff (flatten-ev (conjoin (dumb-flatten-conjunction x)) a)
           (flatten-ev x a))
      :fn dumb-flatten-conjunction))

  (fty::deffixequiv-mutual dumb-flatten-disjunction))

(define dumb-flatten-clause ((x pseudo-term-listp))
  :returns (new-x pseudo-term-listp)
  (if (atom x)
      nil
    (dumb-disjoin-lit-lists (dumb-flatten-disjunction (car x))
                            (dumb-flatten-clause (cdr x))))
  ///
  (defthm dumb-flatten-clause-correct
    (iff (flatten-ev (disjoin (dumb-flatten-clause x)) a)
         (flatten-ev (disjoin x) a))))

(define dumb-flatten-clause-proc ((x pseudo-term-listp))
  (list (dumb-flatten-clause x))
  ///
  (defthm dumb-flatten-clause-proc-correct
    (implies (and (pseudo-term-listp x)
                  (alistp a)
                  (flatten-ev (conjoin-clauses (dumb-flatten-clause-proc x)) a))
             (flatten-ev (disjoin x) a))
    :rule-classes :clause-processor))

