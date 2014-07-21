; Milawa - A Reflective Theorem Prover
; Copyright (C) 2005-2009 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
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
; Original author: Jared Davis <jared@kookamara.com>

(in-package "MILAWA")
(include-book "../utilities/top")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(definlined logic.variablep (x)
  (declare (xargs :guard t))
  (and (symbolp x)
       (not (equal x t))
       (not (equal x nil))))

(defthm booleanp-of-logic.variablep
  (equal (booleanp (logic.variablep x))
         t)
  :hints(("Goal" :in-theory (enable logic.variablep))))

(defthm symbolp-when-logic.variablep
  (implies (logic.variablep x)
           (equal (symbolp x)
                  t))
  :hints(("Goal" :in-theory (enable logic.variablep))))

(defthm logic.variablep-when-consp
  (implies (consp x)
           (equal (logic.variablep x)
                  nil))
  :hints(("Goal" :in-theory (enable logic.variablep))))


(deflist logic.variable-listp (x)
  (logic.variablep x)
  :elementp-of-nil nil)

(defthm logic.variable-listp-of-sort-symbols-insert
  (equal (logic.variable-listp (sort-symbols-insert a x))
         (and (logic.variablep a)
              (logic.variable-listp x)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.variable-listp-of-sort-symbols
  (equal (logic.variable-listp (sort-symbols x))
         (logic.variable-listp x))
  :hints(("Goal" :induct (cdr-induction x))))


(definlined logic.constantp (x)
  (declare (xargs :guard t))
  (and (tuplep 2 x)
       (equal (first x) 'quote)))

(defthm booleanp-of-logic.constantp
  (equal (booleanp (logic.constantp x))
         t)
  :hints(("Goal" :in-theory (enable logic.constantp))))

(defthm logic.constantp-when-not-consp
  (implies (not (consp x))
           (equal (logic.constantp x)
                  nil))
  :hints(("Goal" :in-theory (enable logic.constantp))))

(defthm logic.constantp-of-list-quote
  (equal (logic.constantp (list 'quote x))
         t)
  :hints(("Goal" :in-theory (enable logic.constantp))))



(definlined logic.unquote (x)
  (declare (xargs :guard (logic.constantp x)))
  (second x))

(defthm logic.unquote-of-list-quote
  (equal (logic.unquote (list 'quote x))
         x)
  :hints(("Goal" :in-theory (enable logic.unquote))))

(defthm logic.unquote-under-iff-when-logic.constantp
  (implies (logic.constantp x)
           (iff (logic.unquote x)
                (not (equal x ''NIL))))
  :hints(("Goal" :in-theory (enable logic.constantp logic.unquote))))

(defthm equal-of-logic.unquote-and-logic.unquote
  (implies (and (logic.constantp x)
                (logic.constantp y))
           (equal (equal (logic.unquote x) (logic.unquote y))
                  (equal x y)))
  :hints(("Goal" :in-theory (enable logic.constantp logic.unquote))))



(deflist logic.constant-listp (x)
  (logic.constantp x)
  :elementp-of-nil nil)

(defthm logic.constantp-of-second-when-logic.constant-listp
  ;; BOZO move to deflist?
  (implies (logic.constant-listp x)
           (equal (logic.constantp (second x))
                  (consp (cdr x)))))

(defthm logic.constantp-of-third-when-logic.constant-listp
  ;; BOZO move to deflist?
  (implies (logic.constant-listp x)
           (equal (logic.constantp (third x))
                  (consp (cdr (cdr x))))))


(deflist logic.none-constantp (x)
  (logic.constantp x)
  :elementp-of-nil nil
  :negatedp t)


(defprojection :list (logic.unquote-list x)
               :element (logic.unquote x)
               :guard (logic.constant-listp x)
               :nil-preservingp t)



(defthm logic.variablep-when-logic.constantp
  (implies (logic.constantp x)
           (equal (logic.variablep x)
                  nil))
  :hints(("Goal" :in-theory (enable logic.variablep logic.constantp))))

(defthm logic.constantp-when-logic.variablep
  (implies (logic.variablep x)
           (equal (logic.constantp x)
                  nil)))




(definlined logic.function-namep (x)
  (declare (xargs :guard t))
  (and (symbolp x)
       (not (memberp x '(nil quote pequal* pnot* por*
                             first second third fourth fifth
                             and or list cond let let*)))))

(defthm booleanp-of-logic.function-namep
  (equal (booleanp (logic.function-namep x))
         t)
  :hints(("Goal" :in-theory (e/d (logic.function-namep)
                                 (memberp-of-cons)))))

(defthm symbolp-when-logic.function-namep
  ;; BOZO these got real expensive somehow
  (implies (logic.function-namep x)
           (equal (symbolp x)
                  t))
  :hints(("Goal" :in-theory (enable logic.function-namep))))

(defthm logic.function-namep-when-consp
  (implies (consp x)
           (equal (logic.function-namep x)
                  nil))
  :hints(("Goal" :in-theory (enable logic.function-namep))))

(defthm logic.constantp-when-cons-of-logic.function-namep
  (implies (logic.function-namep name)
           (equal (logic.constantp (cons name x))
                  nil))
  :hints(("Goal" :in-theory (enable logic.constantp))))

(defthm logic.variablep-of-cons-when-logic.function-namep
  (implies (logic.function-namep name)
           (equal (logic.variablep (cons name x))
                  nil))
  :hints(("Goal" :in-theory (enable logic.variablep))))


(deflist logic.function-symbol-listp (x)
  (logic.function-namep x)
  :elementp-of-nil nil)




(defund logic.flag-term-vars (flag x acc)
  ;; Compute the free variables that occur in a term or term list.  This is
  ;; tail recursive, so we add these variables to the accumulator, acc.
  ;;
  ;; It's odd to introduce this concept here, since we haven't yet defined what
  ;; a term is.  But to define terms, we need to be able to talk about free
  ;; variables within the body of a lambda to ensure they are all bound, which
  ;; is why we need this definition first.
  (declare (xargs :guard (and (or (equal flag 'term)
                                  (equal flag 'list))
                              (true-listp acc))
                  :verify-guards nil))
  (if (equal flag 'term)
      (cond ((logic.constantp x) acc)
            ((logic.variablep x) (cons x acc))
            ((not (consp x))     acc)
            (t                   (logic.flag-term-vars 'list (cdr x) acc)))
    (if (consp x)
        (logic.flag-term-vars 'term (car x)
                              (logic.flag-term-vars 'list (cdr x) acc))
      acc)))

(defthm true-listp-of-logic.flag-term-vars
  (equal (true-listp (logic.flag-term-vars flag x acc))
         (true-listp acc))
  :hints(("Goal" :in-theory (enable logic.flag-term-vars))))

(verify-guards logic.flag-term-vars)

(definlined logic.term-vars (x)
  ;; Compute the free variables that occur in a term.
  (declare (xargs :guard t))
  (logic.flag-term-vars 'term x nil))

(definlined logic.term-list-vars (x)
  ;; Compute the free variables that occur in a term list.
  (declare (xargs :guard t))
  (logic.flag-term-vars 'list x nil))


(defund logic.slow-term-vars (flag x)
  ;; Non-tail-recursive version of logic.flag-term-vars
  (declare (xargs :guard (or (equal flag 'term)
                             (equal flag 'list))))
  (if (equal flag 'term)
      (cond ((logic.constantp x) nil)
            ((logic.variablep x) (list x))
            ((not (consp x))     nil)
            (t                   (logic.slow-term-vars 'list (cdr x))))
    (if (consp x)
        (app (logic.slow-term-vars 'term (car x))
             (logic.slow-term-vars 'list (cdr x)))
      nil)))


(encapsulate
 ()
 (defthmd lemma-for-definition-of-logic.term-vars
   (implies (force (true-listp acc))
            (equal (logic.flag-term-vars flag x acc)
                   (app (logic.slow-term-vars flag x) acc)))
   :hints(("Goal"
           :in-theory (enable logic.flag-term-vars
                              logic.slow-term-vars)
           :induct (logic.flag-term-vars flag x acc))))

 (local (in-theory (enable lemma-for-definition-of-logic.term-vars)))

 (defthmd definition-of-logic.term-vars
   (equal (logic.term-vars x)
          (cond ((logic.constantp x) nil)
                ((logic.variablep x) (list x))
                ((not (consp x))     nil)
                (t                   (logic.term-list-vars (cdr x)))))
   :rule-classes :definition
   :hints(("Goal" :in-theory (enable logic.term-vars
                                     logic.term-list-vars
                                     logic.slow-term-vars))))

 (defthmd definition-of-logic.term-list-vars
   (equal (logic.term-list-vars x)
          (if (consp x)
              (app (logic.term-vars (car x))
                   (logic.term-list-vars (cdr x)))
            nil))
   :rule-classes :definition
   :hints(("Goal" :in-theory (enable logic.term-vars
                                     logic.term-list-vars
                                     logic.slow-term-vars))))

 (defthm logic.flag-term-vars-of-term-removal
   (implies (force (true-listp acc))
            (equal (logic.flag-term-vars 'term x acc)
                   (app (logic.term-vars x) acc)))
   :hints(("Goal" :in-theory (enable logic.term-vars
                                     logic.slow-term-vars))))

 (defthm logic.flag-term-vars-of-list-removal
   (implies (force (true-listp acc))
            (equal (logic.flag-term-vars 'list x acc)
                   (app (logic.term-list-vars x) acc)))
   :hints(("Goal" :in-theory (enable logic.term-list-vars
                                     logic.slow-term-vars)))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition logic.term-vars))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition logic.term-list-vars))))




(defund logic.flag-termp (flag x)
  ;; Recognizer for terms and term lists.  This is only a structural check that
  ;; does no arity checking.
  (declare (xargs :guard (or (equal flag 'term)
                             (equal flag 'list))))
  (if (equal flag 'term)
      ;; Check if x is a term.
      (or (logic.variablep x)
          (logic.constantp x)
          (and (consp x)
               (if (logic.function-namep (car x))
                   (let ((args (cdr x)))
                     (and (true-listp args)
                          (logic.flag-termp 'list args)))
                 (and (tuplep 3 (car x))
                      (let ((lambda-symbol (first (car x)))
                            (formals       (second (car x)))
                            (body          (third (car x)))
                            (actuals       (cdr x)))
                        (and (equal lambda-symbol 'lambda)
                             (true-listp formals)
                             (logic.variable-listp formals)
                             (uniquep formals)
                             (logic.flag-termp 'term body)
                             (subsetp (logic.term-vars body) formals)
                             (equal (len formals) (len actuals))
                             (true-listp actuals)
                             (logic.flag-termp 'list actuals)))))))
    ;; Check if x is a term list.
    (if (consp x)
        (and (logic.flag-termp 'term (car x))
             (logic.flag-termp 'list (cdr x)))
      t)))

(definlined logic.termp (x)
  (declare (xargs :guard t))
  (logic.flag-termp 'term x))

(definlined logic.term-listp (x)
  (declare (xargs :guard t))
  (logic.flag-termp 'list x))

(defthmd definition-of-logic.termp
  (equal (logic.termp x)
         (or (logic.variablep x)
             (logic.constantp x)
             (and (consp x)
                  (if (logic.function-namep (car x))
                      (let ((args (cdr x)))
                        (and (true-listp args)
                             (logic.term-listp args)))
                    (and (tuplep 3 (car x))
                         (let ((lambda-symbol (first (car x)))
                               (formals       (second (car x)))
                               (body          (third (car x)))
                               (actuals       (cdr x)))
                           (and (equal lambda-symbol 'lambda)
                                (true-listp formals)
                                (logic.variable-listp formals)
                                (uniquep formals)
                                (logic.termp body)
                                (subsetp (logic.term-vars body) formals)
                                (equal (len formals) (len actuals))
                                (true-listp actuals)
                                (logic.term-listp actuals))))))))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable logic.termp
                                    logic.term-listp
                                    logic.flag-termp))))

(defthmd definition-of-logic.term-listp
  (equal (logic.term-listp x)
         (if (consp x)
             (and (logic.termp (car x))
                  (logic.term-listp (cdr x)))
           t))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable logic.termp
                                    logic.term-listp
                                    logic.flag-termp))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition logic.termp))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition logic.term-listp))))


(defthm logic.termp-when-not-consp-cheap
  (implies (not (consp x))
           (equal (logic.termp x)
                  (logic.variablep x)))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable definition-of-logic.termp))))

(defthm logic.termp-when-logic.variablep
  (implies (logic.variablep x)
           (equal (logic.termp x)
                  t))
  :hints(("Goal" :in-theory (enable definition-of-logic.termp))))

(defthm logic.termp-when-logic.constantp
  (implies (logic.constantp x)
           (equal (logic.termp x)
                  t))
  :hints(("Goal" :in-theory (enable definition-of-logic.termp))))

(defthm logic.term-listp-when-not-consp
  (implies (not (consp x))
           (equal (logic.term-listp x)
                  t))
  :hints(("Goal" :in-theory (enable definition-of-logic.term-listp))))

(defthm logic.term-listp-of-cons
  (equal (logic.term-listp (cons a x))
         (and (logic.termp a)
              (logic.term-listp x)))
  :hints(("Goal" :in-theory (enable definition-of-logic.term-listp))))

(defthm booleanp-of-logic.term-listp
  (equal (booleanp (logic.term-listp x))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm booleanp-of-logic.termp
  (equal (booleanp (logic.termp x))
         t)
  :hints(("Goal"
          :in-theory (enable definition-of-logic.termp)
          :expand (logic.termp x))))


(deflist logic.term-listp (x)
  (logic.termp x)
  :elementp-of-nil nil
  :already-definedp t)

(defthm logic.term-listp-when-logic.constant-listp-cheap
  (implies (logic.constant-listp x)
           (equal (logic.term-listp x)
                  t))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.term-listp-when-logic.variable-listp-cheap
  (implies (logic.variable-listp x)
           (logic.term-listp x))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.term-listp-of-sort-symbols-when-logic.variable-listp
  (implies (logic.variable-listp x)
           (logic.term-listp (sort-symbols x))))



(definlined logic.functionp (x)
  (declare (xargs :guard (logic.termp x)))
  (logic.function-namep (car x)))

(definlined logic.function (name args)
  (declare (xargs :guard (and (logic.function-namep name)
                              (true-listp args)
                              (logic.term-listp args))))
  (cons name args))

(definlined logic.function-name (x)
  (declare (xargs :guard (and (logic.termp x)
                              (logic.functionp x))))
  (car x))

(definlined logic.function-args (x)
  (declare (xargs :guard (and (logic.termp x)
                              (logic.functionp x))))
  (cdr x))

(in-theory (disable (:e logic.function)))

(defthm booleanp-of-logic.functionp
  (equal (booleanp (logic.functionp x))
         t)
  :hints(("Goal" :in-theory (enable logic.functionp))))

(defthm consp-when-logic.functionp-cheap
  (implies (logic.functionp x)
           (equal (consp x)
                  t))
  :rule-classes ((:rewrite :backchain-limit-lst 0))
  :hints(("Goal" :in-theory (enable logic.functionp))))

(defthm logic.variablep-when-logic.functionp
  (implies (logic.functionp x)
           (equal (logic.variablep x)
                  nil))
  :hints(("Goal" :in-theory (enable logic.functionp))))

(defthm logic.constantp-when-logic.functionp
  (implies (logic.functionp x)
           (equal (logic.constantp x)
                  nil))
  :hints(("Goal" :in-theory (enable logic.functionp))))

(defthm consp-of-logic.function
  (equal (consp (logic.function name args))
         t)
  :hints(("Goal" :in-theory (enable logic.function))))

(defthm logic.function-under-iff
  (iff (logic.function name args)
       t)
  :hints(("Goal" :in-theory (enable logic.function))))

(defthm forcing-logic.constantp-of-logic.function
  (implies (force (logic.function-namep name))
           (equal (logic.constantp (logic.function name args))
                  nil))
  :hints(("Goal" :in-theory (enable logic.function))))

(defthm forcing-logic.variablep-of-logic.function
  (implies (force (logic.function-namep name))
           (equal (logic.variablep (logic.function name args))
                  nil))
  :hints(("Goal" :in-theory (enable logic.function))))

(defthm forcing-logic.termp-of-logic.function
  (implies (and (force (logic.function-namep name))
                (force (true-listp args))
                (force (logic.term-listp args)))
           (equal (logic.termp (logic.function name args))
                  t))
  :hints(("Goal" :in-theory (enable logic.function
                                    definition-of-logic.termp))))

(defthm forcing-logic.functionp-of-logic.function
  (implies (force (logic.function-namep name))
           (equal (logic.functionp (logic.function name args))
                  t))
  :hints(("Goal" :in-theory (enable logic.functionp
                                    logic.function))))

(defthm forcing-logic.function-namep-of-logic.function-name
  (implies (force (logic.functionp x))
           (equal (logic.function-namep (logic.function-name x))
                  t))
  :hints(("Goal" :in-theory (enable logic.functionp
                                    logic.function-name
                                    definition-of-logic.termp))))

(defthm logic.function-name-of-logic.function
  (equal (logic.function-name (logic.function name args))
         name)
  :hints(("Goal" :in-theory (enable logic.function-name
                                    logic.function))))

(defthm forcing-true-listp-of-logic.function-args
  (implies (and (force (logic.functionp x))
                (force (logic.termp x)))
           (equal (true-listp (logic.function-args x))
                  t))
  :hints(("Goal" :in-theory (enable logic.functionp
                                    logic.function-args
                                    definition-of-logic.termp))))

(defthm forcing-logic.term-listp-of-logic.function-args
  (implies (and (force (logic.functionp x))
                (force (logic.termp x)))
           (equal (logic.term-listp (logic.function-args x))
                  t))
  :hints(("Goal" :in-theory (enable logic.functionp
                                    logic.function-args
                                    definition-of-logic.termp))))

(defthm logic.function-args-of-logic.function
  (equal (logic.function-args (logic.function name args))
         args)
  :hints(("Goal" :in-theory (enable logic.function-args
                                    logic.function))))

(defthm forcing-logic.function-of-logic.function-name-and-logic.function-args
  (implies (force (logic.functionp x))
           (equal (logic.function (logic.function-name x) (logic.function-args x))
                  x))
  :hints(("Goal" :in-theory (enable logic.functionp
                                    logic.function
                                    logic.function-name
                                    logic.function-args))))

(defthm logic.function-of-logic.function-name-and-nil-when-nil-logic.function-args
  (implies (and (not (logic.function-args x))
                (force (logic.functionp x)))
           (equal (logic.function (logic.function-name x) nil)
                  x))
  :hints(("Goal" :in-theory (enable logic.functionp
                                    logic.function-name
                                    logic.function
                                    logic.function-args))))

(defthm forcing-logic.function-of-logic.function-name-and-logic.function-args-free
  (implies (and (equal name (logic.function-name term))
                (equal args (logic.function-args term))
                (force (logic.functionp term)))
           (equal (logic.function name args)
                  term))
  :hints(("Goal" :in-theory (enable logic.functionp))))

(defthm rank-of-logic.function-args
  (equal (< (rank (logic.function-args x)) (rank x))
         (consp x))
  :hints(("Goal" :in-theory (enable logic.function-args))))

(defthm rank-of-first-of-logic.function-args
  (equal (< (rank (first (logic.function-args x))) (rank x))
         (consp x))
  :hints(("Goal" :in-theory (enable logic.function-args))))

(defthm rank-of-second-of-logic.function-args
  (equal (< (rank (second (logic.function-args x))) (rank x))
         (consp x))
  :hints(("Goal" :in-theory (enable logic.function-args))))

(defthm rank-of-third-of-logic.function-args
  (equal (< (rank (third (logic.function-args x))) (rank x))
         (consp x))
  :hints(("Goal" :in-theory (enable logic.function-args))))

(defthm equal-of-logic.function-rewrite
  (implies (force (logic.function-namep name))
           (equal (equal (logic.function name args) x)
                  (and (logic.functionp x)
                       (equal (logic.function-name x) name)
                       (equal (logic.function-args x) args))))
  :hints(("Goal" :in-theory (enable logic.function
                                    logic.functionp
                                    logic.function-name
                                    logic.function-args))))

(defthm equal-of-logic.function-and-logic.function
  (equal (equal (logic.function name1 args1)
                (logic.function name2 args2))
         (and (equal name1 name2)
              (equal args1 args2)))
  :hints(("Goal" :in-theory (enable logic.function))))

(defthm logic.function-args-under-iff-with-len-free
  (implies (and (equal (len (logic.function-args term)) n)
                (syntaxp (ACL2::quotep n))
                (< 0 n))
           (iff (logic.function-args term)
                t)))

(defthm forcing-equal-of-logic.function-with-two-args
   (implies (and (equal (len (logic.function-args x)) 2)
                 (force (logic.termp x))
                 (force (logic.functionp x)))
            (equal (equal (logic.function name (list a b)) x)
                   (and (equal name (logic.function-name x))
                        (equal a (first (logic.function-args x)))
                        (equal b (second (logic.function-args x)))))))

(defthm forcing-equal-of-logic.function-with-three-args
  (implies (and (equal (len (logic.function-args x)) 3)
                (force (logic.termp x))
                (force (logic.functionp x)))
           (equal (equal (logic.function name (list a b c)) x)
                  (and (equal name (logic.function-name x))
                       (equal a (first (logic.function-args x)))
                       (equal b (second (logic.function-args x)))
                       (equal c (third (logic.function-args x)))))))




(definlined logic.lambdap (x)
  (declare (xargs :guard (logic.termp x)))
  (consp (car x)))

(defthm booleanp-of-logic.lambdap
  (equal (booleanp (logic.lambdap x))
         t)
  :hints(("Goal" :in-theory (enable logic.lambdap))))

(defthm consp-when-logic.lambdap-cheap
  (implies (logic.lambdap x)
           (equal (consp x)
                  t))
  :rule-classes ((:rewrite :backchain-limit-lst 0))
  :hints(("Goal" :in-theory (enable logic.lambdap))))

(defthm logic.variablep-when-logic.lambdap-cheap
  (implies (logic.lambdap x)
           (equal (logic.variablep x)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable logic.lambdap logic.variablep))))

(defthm logic.constantp-when-logic.lambdap-cheap
  (implies (logic.lambdap x)
           (equal (logic.constantp x)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable logic.lambdap logic.constantp))))

(defthm logic.functionp-when-logic.lambdap-cheap
  (implies (logic.lambdap x)
           (equal (logic.functionp x)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable logic.lambdap logic.functionp))))

(defthm logic.lambdap-when-logic.functionp-cheap
  (implies (logic.functionp x)
           (equal (logic.lambdap x)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable logic.lambdap))))




(definlined logic.lambda (xs b ts)
  (declare (xargs :guard (and (true-listp xs)
                              (logic.variable-listp xs)
                              (uniquep xs)
                              (logic.termp b)
                              (true-listp ts)
                              (logic.term-listp ts))))
  (cons (list 'lambda xs b) ts))


(in-theory (disable (:e logic.lambda)))

(defthm consp-of-logic.lambda
  (equal (consp (logic.lambda formals body actuals))
         t)
  :hints(("Goal" :in-theory (enable logic.lambda))))

(defthm logic.lambda-under-iff
  (iff (logic.lambda formals body actuals)
       t)
  :hints(("Goal" :in-theory (enable logic.lambda))))

(defthm logic.constantp-of-logic.lambda
  (equal (logic.constantp (logic.lambda formals body actuals))
         nil)
  :hints(("Goal" :in-theory (enable logic.lambda logic.constantp))))

(defthm logic.variablep-of-logic.lambda
  (equal (logic.variablep (logic.lambda formals body actuals))
         nil)
  :hints(("Goal" :in-theory (enable logic.lambda
                                    logic.variablep))))

(defthm logic.functionp-of-logic.lambda
  (equal (logic.functionp (logic.lambda formals body actuals))
         nil)
  :hints(("Goal" :in-theory (enable logic.lambda
                                    logic.functionp
                                    logic.function-namep))))

(defthm forcing-logic.termp-of-logic.lambda
  (implies (and (force (true-listp formals))
                (force (logic.variable-listp formals))
                (force (uniquep formals))
                (force (logic.termp body))
                (force (subsetp (logic.term-vars body) formals))
                (force (true-listp actuals))
                (force (logic.term-listp actuals))
                (force (equal (len formals) (len actuals))))
           (equal (logic.termp (logic.lambda formals body actuals))
                  t))
  :hints(("Goal" :in-theory (enable logic.lambda
                                    definition-of-logic.termp))))

(defthm logic.lambdap-of-logic.lambda
  (equal (logic.lambdap (logic.lambda formals body actuals))
         t)
  :hints(("Goal" :in-theory (enable logic.lambdap logic.lambda))))

(defthm equal-of-logic.lambda-and-logic.lambda
  (equal (equal (logic.lambda formals1 body1 actuals1)
                (logic.lambda formals2 body2 actuals2))
         (and (equal formals1 formals2)
              (equal body1 body2)
              (equal actuals1 actuals2)))
  :hints(("Goal" :in-theory (enable logic.lambda))))




(definlined logic.lambda-formals (x)
  (declare (xargs :guard (and (logic.termp x)
                              (logic.lambdap x))))
  (second (car x)))

(defthm forcing-true-listp-of-logic.lambda-formals
  (implies (and (force (logic.lambdap x))
                (force (logic.termp x)))
           (equal (true-listp (logic.lambda-formals x))
                  t))
  :hints(("Goal" :in-theory (enable logic.lambdap
                                    logic.lambda-formals
                                    definition-of-logic.termp))))

(defthm forcing-logic.variable-listp-of-logic.lambda-formals
  (implies (and (force (logic.lambdap x))
                (force (logic.termp x)))
           (logic.variable-listp (logic.lambda-formals x)))
  :hints(("Goal" :in-theory (enable logic.lambdap
                                    logic.lambda-formals
                                    definition-of-logic.termp))))

(defthm forcing-uniquep-of-logic.lambda-formals
  (implies (and (force (logic.lambdap x))
                (force (logic.termp x)))
           (uniquep (logic.lambda-formals x)))
  :hints(("Goal" :in-theory (enable logic.lambdap
                                    logic.lambda-formals
                                    definition-of-logic.termp))))

(defthm logic.lambda-formals-of-logic.lambda
  (equal (logic.lambda-formals (logic.lambda formals body actuals))
         formals)
  :hints(("Goal" :in-theory (enable logic.lambda-formals
                                    logic.lambda))))






(definlined logic.lambda-body (x)
  (declare (xargs :guard (and (logic.termp x)
                              (logic.lambdap x))))
  (third (car x)))

(defthm forcing-logic.termp-of-logic.lambda-body
  (implies (and (force (logic.lambdap x))
                (force (logic.termp x)))
           (logic.termp (logic.lambda-body x)))
  :hints(("Goal" :in-theory (enable logic.lambdap
                                    logic.lambda-body
                                    definition-of-logic.termp))))

(defthm logic.lambda-body-of-logic.lambda
  (equal (logic.lambda-body (logic.lambda formals body actuals))
         body)
  :hints(("Goal" :in-theory (enable logic.lambda-body logic.lambda))))

(defthm rank-of-logic.lambda-body
  (equal (< (rank (logic.lambda-body x)) (rank x))
         (consp x))
  :hints(("Goal" :in-theory (enable logic.lambda-body))))

(defthm forcing-subsetp-of-logic.term-vars-of-logic.lambda-body-with-logic.lambda-formals
  (implies (and (force (logic.lambdap x))
                (force (logic.termp x)))
           (equal (subsetp (logic.term-vars (logic.lambda-body x))
                           (logic.lambda-formals x))
                  t))
  :hints(("Goal" :in-theory (enable definition-of-logic.termp
                                    logic.lambdap
                                    logic.lambda-body
                                    logic.lambda-formals))))



(definlined logic.lambda-actuals (x)
  (declare (xargs :guard (and (logic.termp x)
                              (logic.lambdap x))))
  (cdr x))

(defthm forcing-true-listp-of-logic.lambda-actuals
  (implies (and (force (logic.lambdap x))
                (force (logic.termp x)))
           (equal (true-listp (logic.lambda-actuals x))
                  t))
  :hints(("Goal" :in-theory (enable logic.lambdap
                                    logic.lambda-actuals
                                    definition-of-logic.termp))))

(defthm forcing-logic.term-listp-of-logic.lambda-actuals
  (implies (and (force (logic.lambdap x))
                (force (logic.termp x)))
           (equal (logic.term-listp (logic.lambda-actuals x))
                  t))
  :hints(("Goal" :in-theory (enable logic.lambdap
                                    logic.lambda-actuals
                                    definition-of-logic.termp))))

(defthm logic.lambda-actuals-of-logic.lambda
  (equal (logic.lambda-actuals (logic.lambda formals body actuals))
         actuals)
  :hints(("Goal" :in-theory (enable logic.lambda-actuals logic.lambda))))





(defthm forcing-equal-lens-of-logic.lambda-formals-and-logic.lambda-actuals
  ;; The lengths of the actuals and formals are equal, so we choose to
  ;; canonicalize one to the other.  Originally I had chosen the length of the
  ;; formals as the normal form.  But in obscure cases, this could lead the
  ;; rewriter to loop.  For example, suppose the rewriter has discovered on
  ;; its own that the lengths are equal.  Then, we can get the following loop:
  ;;
  ;;   1. Rewrite (len actuals) to (len formals)
  ;;   2. Canonicalize (len formals) back to (len actuals), since
  ;;      "(len (logic.lambda-actuals x))" is term-< than "(len (logic.lambda-formals x))"
  ;;
  ;; So, now we use the length of the actuals as the normal form, since now
  ;; term-< canonicalization agrees with the way we are trying to normalize.
  (implies (and (force (logic.lambdap x))
                (force (logic.termp x)))
           (equal (len (logic.lambda-formals x))
                  (len (logic.lambda-actuals x))))
  :hints(("Goal" :in-theory (enable definition-of-logic.termp
                                    logic.lambdap
                                    logic.lambda-formals
                                    logic.lambda-actuals))))

(defthm forcing-logic.lambda-of-logic.lambda-formals-body-and-actuals
  (implies (and (force (logic.lambdap x))
                (force (logic.termp x)))
           (equal (logic.lambda (logic.lambda-formals x)
                                (logic.lambda-body x)
                                (logic.lambda-actuals x))
                  x))
  :hints(("Goal" :in-theory (enable logic.lambdap
                                    logic.lambda
                                    logic.lambda-formals
                                    logic.lambda-body
                                    logic.lambda-actuals
                                    definition-of-logic.termp))))

(defthm forcing-logic.lambda-of-logic.lambda-formals-body-and-actuals-free
  (implies (and (equal formals (logic.lambda-formals x))
                (equal body (logic.lambda-body x))
                (equal actuals (logic.lambda-actuals x))
                (force (logic.lambdap x))
                (force (logic.termp x)))
           (equal (logic.lambda formals body actuals)
                  x)))

(defthm rank-of-logic.lambda-actuals
  (equal (< (rank (logic.lambda-actuals x)) (rank x))
         (consp x))
  :hints(("Goal" :in-theory (enable logic.lambda-actuals))))

(defthm rank-of-first-of-logic.lambda-actuals
  (equal (< (rank (logic.lambda-actuals x)) (rank x))
         (consp x))
  :hints(("Goal" :in-theory (enable logic.lambda-actuals))))

(defthm rank-of-second-of-logic.lambda-actuals
  (equal (< (rank (second (logic.lambda-actuals x))) (rank x))
         (consp x))
  :hints(("Goal" :in-theory (enable logic.lambda-actuals))))

(defthm rank-of-third-of-logic.lambda-actuals
  (equal (< (rank (third (logic.lambda-actuals x))) (rank x))
         (consp x))
  :hints(("Goal" :in-theory (enable logic.lambda-actuals))))


(defthm logic.function-namep-of-car-when-logic.termp-and-not-logic.variablep
  (implies (and (logic.termp x)
                (not (logic.variablep x)))
           (equal (logic.function-namep (car x))
                  (logic.functionp x)))
  :hints(("Goal" :in-theory (enable definition-of-logic.termp
                                    logic.functionp))))

(defthm logic.lambdap-when-not-anything-else-maybe-expensive
  (implies (and (logic.termp x)
                (not (logic.constantp x))
                (not (logic.variablep x))
                (not (logic.functionp x)))
           (equal (logic.lambdap x)
                  t))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable definition-of-logic.termp
                                    logic.lambdap
                                    logic.functionp))))

(defthm logic.termp-when-invalid-maybe-expensive
  (implies (and (not (logic.variablep x))
                (not (logic.constantp x))
                (not (logic.functionp x))
                (not (logic.lambdap x)))
           (equal (logic.termp x)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))

(defthm logic.functionp-when-not-other-stuff-cheap
  (implies (and (logic.termp x)
                (not (logic.variablep x))
                (not (logic.constantp x))
                (not (logic.lambdap x)))
           (equal (logic.functionp x)
                  t))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm logic.lambdap-when-not-other-stuff-cheap
  (implies (and (logic.termp x)
                (not (logic.variablep x))
                (not (logic.constantp x))
                (not (logic.functionp x)))
           (equal (logic.lambdap x)
                  t))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm logic.lambdap-when-consp-of-car-cheap
  (implies (and (logic.termp x)
                (consp (car x)))
           (equal (logic.lambdap x)
                  t))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable logic.lambdap))))







(defun logic.term-induction (flg x)
  (declare (xargs :verify-guards nil))
  (if (equal flg 'term)
      (cond ((logic.variablep x) nil)
            ((logic.constantp x) nil)
            ((logic.functionp x)
             (logic.term-induction 'list (logic.function-args x)))
            ((logic.lambdap x)
             (list (logic.term-induction 'term (logic.lambda-body x))
                   (logic.term-induction 'list (logic.lambda-actuals x))))
            (t nil))
    (if (consp x)
        (list (logic.term-induction 'term (car x))
              (logic.term-induction 'list (cdr x)))
      nil)))





(defthm logic.term-list-vars-when-not-consp
  (implies (not (consp x))
           (equal (logic.term-list-vars x)
                  nil))
  :hints(("Goal" :in-theory (enable definition-of-logic.term-list-vars))))

(defthm logic.term-list-vars-of-cons
  (equal (logic.term-list-vars (cons a x))
         (app (logic.term-vars a)
              (logic.term-list-vars x)))
  :hints(("Goal" :in-theory (enable definition-of-logic.term-list-vars))))

(defthm true-listp-of-logic.term-list-vars
  (equal (true-listp (logic.term-list-vars x))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm true-listp-of-logic.term-vars
  (equal (true-listp (logic.term-vars x))
         t)
  :hints(("Goal" :in-theory (enable definition-of-logic.term-vars))))

(defthm logic.term-vars-when-variable
  (implies (logic.variablep x)
           (equal (logic.term-vars x)
                  (list x)))
  :hints(("Goal" :in-theory (enable definition-of-logic.term-vars))))

(defthm logic.term-vars-when-constant
  (implies (logic.constantp x)
           (equal (logic.term-vars x)
                  nil))
  :hints(("Goal" :in-theory (enable definition-of-logic.term-vars))))

(defthm logic.term-vars-when-bad
  (implies (and (not (logic.constantp x))
                (not (logic.variablep x))
                (not (consp x)))
           (equal (logic.term-vars x)
                  nil))
  :hints(("Goal" :in-theory (enable definition-of-logic.term-vars))))

(defthm logic.term-vars-when-function-call
  (implies (logic.functionp x)
           (equal (logic.term-vars x)
                  (logic.term-list-vars (logic.function-args x))))
  :hints(("Goal" :in-theory (enable logic.function-args
                                    definition-of-logic.term-vars))))

(defthm logic.term-vars-when-logic.lambda
  (implies (logic.lambdap x)
           (equal (logic.term-vars x)
                  (logic.term-list-vars (logic.lambda-actuals x))))
  :hints(("Goal"
          :in-theory (enable logic.lambdap logic.lambda-actuals definition-of-logic.term-vars))))

(defthm subsetp-of-logic.term-list-vars-of-cdr-with-logic.term-list-vars
  (equal (subsetp (logic.term-list-vars (cdr x))
                  (logic.term-list-vars x))
         t))

(defthm subsetp-of-logic.term-vars-of-car-with-logic.term-list-vars
  (equal (subsetp (logic.term-vars (car x))
                  (logic.term-list-vars x))
         t))

(defthms-flag
  :thms ((term forcing-logic.variable-listp-of-logic.term-vars
               (implies (force (logic.termp x))
                        (equal (logic.variable-listp (logic.term-vars x))
                               t)))
         (t forcing-logic.variable-listp-of-logic.term-list-vars
            (implies (force (logic.term-listp x))
                     (equal (logic.variable-listp (logic.term-list-vars x))
                            t))))
  :hints(("Goal"
          :induct (logic.term-induction flag x)
          :in-theory (enable definition-of-logic.term-vars))))

(defthm logic.term-list-vars-when-logic.variable-listp
  (implies (logic.variable-listp x)
           (equal (logic.term-list-vars x)
                  (list-fix x)))
  :hints(("Goal" :induct (cdr-induction x))))

(encapsulate
 ()
 (defthmd lemma-for-subsetp-of-logic.term-list-vars-and-remove-duplicates
   (implies (memberp a x)
            (subsetp (logic.term-vars a) (logic.term-list-vars x)))
   :hints(("Goal" :induct (cdr-induction x))))

 (defthm subsetp-of-logic.term-list-vars-and-remove-duplicates
   (subsetp (logic.term-list-vars x)
            (logic.term-list-vars (remove-duplicates x)))
   :hints(("Goal"
           :induct (cdr-induction x)
           :in-theory (enable lemma-for-subsetp-of-logic.term-list-vars-and-remove-duplicates)))))

(defthm subsetp-of-logic.term-list-vars-and-remove-duplicates-two
  (subsetp (logic.term-list-vars (remove-duplicates x))
           (logic.term-list-vars x))
  :hints(("Goal" :induct (cdr-induction x))))



(deflist logic.term-list-listp (x)
  (logic.term-listp x)
  :elementp-of-nil t)

(defthm logic.term-listp-when-subset-of-somep
  (implies (and (subset-of-somep a x)
                (logic.term-list-listp x))
           (equal (logic.term-listp a)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.term-listp-when-subset-of-somep-alt
  (implies (and (logic.term-list-listp x)
                (subset-of-somep a x))
           (equal (logic.term-listp a)
                  t)))

(defthm logic.term-list-listp-when-all-superset-of-somep
  (implies (and (all-subset-of-somep x y)
                (logic.term-list-listp y))
           (equal (logic.term-list-listp x)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.term-list-listp-when-all-superset-of-somep-alt
  (implies (and (logic.term-list-listp y)
                (all-subset-of-somep x y))
           (equal (logic.term-list-listp x)
                  t)))

(defthm forcing-logic.term-list-listp-of-remove-supersets1
  (implies (and (force (logic.term-list-listp todo))
                (force (logic.term-list-listp done)))
           (equal (logic.term-list-listp (remove-supersets1 todo done))
                  t))
  :hints(("Goal" :in-theory (enable remove-supersets1))))

(defthm forcing-logic.term-list-listp-of-remove-supersets
  (implies (force (logic.term-list-listp x))
           (equal (logic.term-list-listp (remove-supersets x))
                  t))
  :hints(("Goal" :in-theory (enable remove-supersets))))

(defthm forcing-logic.term-list-listp-of-remove-duplicates-list
  (implies (force (logic.term-list-listp x))
           (equal (logic.term-list-listp (remove-duplicates-list x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.term-listp-of-strip-firsts-when-logic.term-list-listp
  (implies (force (and (logic.term-list-listp x)
                       (all-at-leastp 1 (strip-lens x))))
           (equal (logic.term-listp (strip-firsts x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.term-list-listp-of-listify-each
  (implies (force (logic.term-listp x))
           (equal (logic.term-list-listp (listify-each x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.term-listp-of-simple-flatten
  (implies (force (logic.term-list-listp x))
           (equal (logic.term-listp (simple-flatten x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.term-list-listp-of-multicons
  (implies (and (force (logic.termp e))
                (force (logic.term-list-listp x)))
           (equal (logic.term-list-listp (multicons e x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))




(defund logic.fast-term-list-list-vars (x acc)
  (declare (xargs :guard (and (logic.term-list-listp x)
                              (true-listp acc))
                  :verify-guards nil))
  (if (consp x)
      (logic.flag-term-vars 'list (car x)
                            (logic.fast-term-list-list-vars (cdr x) acc))
    acc))

(defthm true-listp-of-logic.fast-term-list-list-vars
  (equal (true-listp (logic.fast-term-list-list-vars x acc))
         (true-listp acc))
  :hints(("Goal" :in-theory (enable logic.fast-term-list-list-vars))))

(verify-guards logic.fast-term-list-list-vars)


(definlined logic.term-list-list-vars (x)
  (declare (xargs :guard (logic.term-list-listp x)))
  (logic.fast-term-list-list-vars x nil))

(defthmd definition-of-logic.term-list-list-vars
  (equal (logic.term-list-list-vars x)
         (if (consp x)
             (app (logic.term-list-vars (car x))
                  (logic.term-list-list-vars (cdr x)))
           nil))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable logic.term-list-list-vars
                                    logic.fast-term-list-list-vars))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition logic.term-list-list-vars))))

(defthm true-listp-of-logic.term-list-list-vars
  (equal (true-listp (logic.term-list-list-vars x))
         t)
  :hints(("Goal"
          :in-theory (enable definition-of-logic.term-list-list-vars)
          :induct (cdr-induction x))))

(defthm logic.term-list-list-vars-when-not-consp
  (implies (not (consp x))
           (equal (logic.term-list-list-vars x)
                  nil))
  :hints(("Goal" :in-theory (enable definition-of-logic.term-list-list-vars))))

(defthm logic.term-list-list-vars-of-cons
  (equal (logic.term-list-list-vars (cons a x))
         (app (logic.term-list-vars a)
              (logic.term-list-list-vars x)))
  :hints(("Goal" :in-theory (enable definition-of-logic.term-list-list-vars))))

(defthm forcing-logic.variable-listp-of-logic.term-list-list-vars
  (implies (force (logic.term-list-listp x))
           (equal (logic.variable-listp (logic.term-list-list-vars x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))




(defthm first-under-iff-when-logic.term-listp-with-len-free
  (implies (and (equal (len x) n)
                (syntaxp (ACL2::quotep n))
                (logic.term-listp x)
                (< 0 n))
           (iff (first x)
                t)))

(defthm second-under-iff-when-logic.term-listp-with-len-free
  (implies (and (equal (len x) n)
                (syntaxp (ACL2::quotep n))
                (logic.term-listp x)
                (< 1 n))
           (iff (second x)
                t)))

(defthm third-under-iff-when-logic.term-listp-with-len-free
  (implies (and (equal (len x) n)
                (syntaxp (ACL2::quotep n))
                (logic.term-listp x)
                (< 2 n))
           (iff (third x)
                t)))




(defmap :map (logic.arity-tablep x)
        :key (logic.function-namep x)
        :val (natp x)
        :key-list (logic.function-symbol-listp x)
        :val-list (nat-listp x)
        :val-of-nil nil)

(encapsulate
 ()
 (local (ACL2::allow-fertilize t))
 (defthm logic.arity-tablep-of-halve-list
   (equal (logic.arity-tablep x)
          (and (logic.arity-tablep (car (halve-list x)))
               (logic.arity-tablep (cdr (halve-list x)))))
   :rule-classes nil
   :hints(("Goal"
           :in-theory (disable halve-list-correct
                               logic.arity-tablep-of-list-fix
                               logic.arity-tablep-of-subset-when-logic.arity-tablep)
           :use ((:instance halve-list-correct)
                 (:instance logic.arity-tablep-of-list-fix)))))

 (defthm logic.arity-tablep-of-halve-list-1
   (implies (logic.arity-tablep x)
            (logic.arity-tablep (car (halve-list x))))
   :hints(("Goal" :use ((:instance logic.arity-tablep-of-halve-list)))))

 (defthm logic.arity-tablep-of-halve-list-2
   (implies (logic.arity-tablep x)
            (logic.arity-tablep (cdr (halve-list x))))
   :hints(("Goal" :use ((:instance logic.arity-tablep-of-halve-list))))))

(defthm logic.arity-tablep-of-merge-maps
  (implies (and (force (logic.arity-tablep x))
                (force (logic.arity-tablep y)))
           (equal (logic.arity-tablep (merge-maps x y))
                  t))
  :hints(("Goal" :in-theory (enable merge-maps))))

(defthm logic.arity-tablep-of-mergesort-map
  (implies (logic.arity-tablep x)
           (logic.arity-tablep (mergesort-map x)))
  :hints(("Goal"
          :in-theory (enable mergesort-map))))



(defund logic.flag-term-atblp (flag x atbl)
  ;; Check if every function call throughout the term(-list) has the arity
  ;; specified in the arity table.
  (declare (xargs :guard (and (if (equal flag 'term)
                                  (logic.termp x)
                                (and (equal flag 'list)
                                     (logic.term-listp x)))
                              (logic.arity-tablep atbl))))
  (if (equal flag 'term)
      (cond ((logic.constantp x)
             t)
            ((logic.variablep x)
             t)
            ((logic.functionp x)
             (let ((name (logic.function-name x))
                   (args (logic.function-args x)))
               (and (equal (len args) (cdr (lookup name atbl)))
                    (logic.flag-term-atblp 'list args atbl))))
            ((logic.lambdap x)
             (let ((body (logic.lambda-body x))
                   (actuals (logic.lambda-actuals x)))
               (and (logic.flag-term-atblp 'term body atbl)
                    (logic.flag-term-atblp 'list actuals atbl))))
            (t nil))
    (if (consp x)
        (and (logic.flag-term-atblp 'term (car x) atbl)
             (logic.flag-term-atblp 'list (cdr x) atbl))
     t)))

(definlined logic.term-atblp (x atbl)
  (declare (xargs :guard (and (logic.termp x)
                              (logic.arity-tablep atbl))))
  (logic.flag-term-atblp 'term x atbl))

(definlined logic.term-list-atblp (x atbl)
  (declare (xargs :guard (and (logic.term-listp x)
                              (logic.arity-tablep atbl))))
  (logic.flag-term-atblp 'list x atbl))

(defthmd definition-of-logic.term-atblp
  (equal (logic.term-atblp x atbl)
         (cond ((logic.constantp x)
                t)
               ((logic.variablep x)
                t)
               ((logic.functionp x)
                (let ((name (logic.function-name x))
                      (args (logic.function-args x)))
                  (and (equal (len args) (cdr (lookup name atbl)))
                       (logic.term-list-atblp args atbl))))
               ((logic.lambdap x)
                (let ((body (logic.lambda-body x))
                      (actuals (logic.lambda-actuals x)))
               (and (logic.term-atblp body atbl)
                    (logic.term-list-atblp actuals atbl))))
               (t nil)))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable logic.term-atblp
                                    logic.term-list-atblp
                                    logic.flag-term-atblp))))

(defthmd definition-of-logic.term-list-atblp
  (equal (logic.term-list-atblp x atbl)
         (if (consp x)
             (and (logic.term-atblp (car x) atbl)
                  (logic.term-list-atblp (cdr x) atbl))
           t))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable logic.term-atblp
                                    logic.term-list-atblp
                                    logic.flag-term-atblp))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition logic.term-atblp))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition logic.term-list-atblp))))


(defthm logic.term-list-atblp-when-not-consp
  (implies (not (consp x))
           (equal (logic.term-list-atblp x atbl)
                  t))
  :hints(("Goal" :in-theory (enable definition-of-logic.term-list-atblp))))

(defthm logic.term-list-atblp-of-cons
  (equal (logic.term-list-atblp (cons a x) atbl)
         (and (logic.term-atblp a atbl)
              (logic.term-list-atblp x atbl)))
  :hints(("Goal" :in-theory (enable definition-of-logic.term-list-atblp))))

(defthms-flag
  :thms ((term booleanp-of-logic.term-atblp
               (equal (booleanp (logic.term-atblp x atbl))
                      t))
         (t booleanp-of-logic.term-list-atblp
            (equal (booleanp (logic.term-list-atblp x atbl))
                   t)))
  :hints(("Goal"
          :induct (logic.term-induction flag x)
          :in-theory (enable definition-of-logic.term-atblp))))

(defthm logic.term-atblp-of-nil
  (equal (logic.term-atblp nil atbl)
         nil)
  :hints(("Goal" :in-theory (enable definition-of-logic.term-atblp))))

(deflist logic.term-list-atblp (x atbl)
  (logic.term-atblp x atbl)
  :elementp-of-nil nil
  :already-definedp t)

(deflist logic.term-list-list-atblp (x atbl)
  (logic.term-list-atblp x atbl)
  :elementp-of-nil t
  :guard (and (logic.term-list-listp x)
              (logic.arity-tablep atbl)))

(defthm logic.term-atblp-when-logic.variablep
  (implies (logic.variablep x)
           (equal (logic.term-atblp x atbl)
                  t))
  :hints(("Goal" :in-theory (enable definition-of-logic.term-atblp))))

(defthm logic.term-atblp-when-logic.constantp
  (implies (logic.constantp x)
           (equal (logic.term-atblp x atbl)
                  t))
  :hints(("Goal" :in-theory (enable definition-of-logic.term-atblp))))

(defthm logic.term-list-atblp-when-logic.constant-listp
  (implies (logic.constant-listp x)
           (equal (logic.term-list-atblp x atbl)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.term-list-atblp-when-logic.variable-listp
  (implies (logic.variable-listp x)
           (equal (logic.term-list-atblp x atbl)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.term-atblp-of-logic.function
  (implies (and (force (logic.function-namep name))
                (force (logic.term-list-atblp args atbl))
                (force (equal (cdr (lookup name atbl)) (len args))))
           (equal (logic.term-atblp (logic.function name args) atbl)
                  t))
  :hints(("Goal" :in-theory (enable definition-of-logic.term-atblp))))

(defthm forcing-logic.term-atblp-of-logic.lambda
  (implies (and (force (logic.term-atblp body atbl))
                (force (logic.term-list-atblp actuals atbl)))
           (equal (logic.term-atblp (logic.lambda formals body actuals) atbl)
                  t))
  :hints(("Goal" :in-theory (e/d (definition-of-logic.term-atblp)
                                 ;; Leads to inappropriate forcing
                                 (logic.lambdap-when-not-anything-else-maybe-expensive)))))

(defthm forcing-logic.term-list-atblp-of-logic.function-args
  ;; BOZO why aren't we forcing both hyps?
  ;; I'm now trying to force them both.  Previously I wasn't forcing the first one
  ;; for some reason.
  (implies (and (force (logic.term-atblp x atbl))
                (force (logic.functionp x)))
           (equal (logic.term-list-atblp (logic.function-args x) atbl)
                  t))
  :hints(("Goal" :in-theory (enable definition-of-logic.term-atblp))))

(defthm forcing-logic.term-list-atblp-of-logic.lambda-actuals
  ;; BOZO why aren't we forcing both hyps?
  ;; Same as above.
  (implies (and (force (logic.term-atblp x atbl))
                (force (logic.lambdap x)))
           (equal (logic.term-list-atblp (logic.lambda-actuals x) atbl)
                  t))
  :hints(("Goal" :in-theory (enable definition-of-logic.term-atblp))))

(defthm forcing-logic.term-atblp-of-logic.lambda-body
  ;; I've sometimes had trouble with this rule forcibly picking up the wrong
  ;; arity table.  I prefer to still force it, and use a :restrict hint when it
  ;; gets into trouble.
  (implies (and (force (logic.term-atblp x atbl))
                (force (logic.lambdap x)))
           (equal (logic.term-atblp (logic.lambda-body x) atbl)
                  t))
  :hints(("Goal" :in-theory (enable definition-of-logic.term-atblp))))

(defthm logic.term-list-atblp-of-strip-firsts-when-logic.term-list-listp
  (implies (force (and (logic.term-list-list-atblp x atbl)
                       (all-at-leastp 1 (strip-lens x))))
           (equal (logic.term-list-atblp (strip-firsts x) atbl)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))


(encapsulate
 ()
 (defthmd lemma-for-forcing-lookup-of-logic.function-name
   (implies (and (equal (cdr (lookup key map)) value)
                 (natp value))
            (lookup key map)))

 (defthm forcing-lookup-of-logic.function-name
   ;; I've sometimes had trouble with this rule forcibly picking up the wrong
   ;; arity table.  I prefer to still force it, and use a :restrict hint when it
   ;; gets into trouble.
   ;; Bleh, I'm going to change it to restricted atbls here.
   (implies (and (syntaxp (equal atbl 'atbl))
                 (force (logic.term-atblp x atbl))
                 (force (logic.functionp x)))
            (equal (lookup (logic.function-name x) atbl)
                   (cons (logic.function-name x) (len (logic.function-args x)))))
   :hints(("Goal" :in-theory (e/d (definition-of-logic.term-atblp
                                    lemma-for-forcing-lookup-of-logic.function-name)
                                  (forcing-logic.term-list-atblp-of-logic.function-args))))))

(defthm forcing-lookup-of-logic.function-name-free
  ;; Added syntaxp here too.
  (implies (and (syntaxp (equal atbl 'atbl))
                (equal (logic.function-name x) name)
                (force (logic.term-atblp x atbl))
                (force (logic.functionp x)))
           (equal (lookup name atbl)
                  (cons name (len (logic.function-args x))))))



(encapsulate
 ()
 (defthmd lemma-1-for-logic.term-atblp-when-logic.term-atblp-in-smaller-arity-table
   (implies (natp (cdr (lookup name atbl)))
            (equal (consp (lookup name atbl))
                   t)))

 (defthmd lemma-2-for-logic.term-atblp-when-logic.term-atblp-in-smaller-arity-table
   (implies (and (submapp atbl atbl2)
                 (natp (cdr (lookup name atbl))))
            (equal (lookup name atbl2)
                   (lookup name atbl)))
   :hints(("Goal"
           :in-theory (disable equal-of-lookups-when-submapp)
           :use ((:instance equal-of-lookups-when-submapp
                            (a name) (x atbl) (y atbl2))))))

 (defthms-flag
   :thms ((term logic.term-atblp-when-logic.term-atblp-in-smaller-arity-table
                (implies (and (submapp atbl atbl2)
                              (logic.term-atblp x atbl))
                         (equal (logic.term-atblp x atbl2)
                                t)))
          (t logic.term-list-atblp-when-logic.term-list-atblp-in-smaller-arity-table
             (implies (and (submapp atbl atbl2)
                           (logic.term-list-atblp x atbl))
                      (equal (logic.term-list-atblp x atbl2)
                             t))))
   :hints(("Goal"
           :induct (logic.term-induction flag x)
           :in-theory (e/d (definition-of-logic.term-atblp
                             lemma-1-for-logic.term-atblp-when-logic.term-atblp-in-smaller-arity-table
                             lemma-2-for-logic.term-atblp-when-logic.term-atblp-in-smaller-arity-table)
                           (forcing-logic.term-atblp-of-logic.lambda-body))))))

(defthm logic.term-atblp-when-logic.term-atblp-in-smaller-arity-table-alt
  (implies (and (logic.term-atblp x atbl)
                (submapp atbl atbl2))
           (equal (logic.term-atblp x atbl2)
                  t)))

(defthm logic.term-list-atblp-when-logic.term-list-atblp-in-smaller-arity-table-alt
  (implies (and (logic.term-list-atblp x atbl)
                (submapp atbl atbl2))
           (equal (logic.term-list-atblp x atbl2)
                  t)))


(defthm logic.term-atblp-when-malformed-cheap
  (implies (and (not (logic.constantp x))
                (not (logic.variablep x))
                (not (logic.functionp x))
                (not (logic.lambdap x)))
           (equal (logic.term-atblp x atbl)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst 0))
  :hints(("Goal" :in-theory (enable definition-of-logic.term-atblp))))
