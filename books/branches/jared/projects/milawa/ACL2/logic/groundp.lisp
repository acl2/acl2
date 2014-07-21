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
(include-book "substitute-term")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


;; (logic.groundp x)             (also logic.fast-groundp)
;; (logic.ground-listp x)        (also logic.fast-ground-listp)
;;
;; Recognizers for variable-free ("ground") terms and term lists.

(defund logic.flag-groundp (flag x)
  (declare (xargs :guard (if (equal flag 'term)
                             (logic.termp x)
                           (logic.term-listp x))))
  (if (equal flag 'term)
      (cond ((logic.constantp x)
             t)
            ((logic.variablep x)
             nil)
            ((logic.functionp x)
             (logic.flag-groundp 'list (logic.function-args x)))
            ((logic.lambdap x)
             (logic.flag-groundp 'list (logic.lambda-actuals x)))
            (t nil))
    (if (consp x)
        (and (logic.flag-groundp 'term (car x))
             (logic.flag-groundp 'list (cdr x)))
      t)))

(definlined logic.groundp (x)
  (declare (xargs :guard (logic.termp x)))
  (logic.flag-groundp 'term x))

(definlined logic.ground-listp (x)
  (declare (xargs :guard (logic.term-listp x)))
  (logic.flag-groundp 'list x))

(defthmd definition-of-logic.groundp
  (equal (logic.groundp x)
         (cond ((logic.constantp x)
                t)
               ((logic.variablep x)
                nil)
               ((logic.functionp x)
                (logic.ground-listp (logic.function-args x)))
               ((logic.lambdap x)
                (logic.ground-listp (logic.lambda-actuals x)))
               (t nil)))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable logic.flag-groundp
                                    logic.groundp
                                    logic.ground-listp))))

(defthmd definition-of-logic.ground-listp
  (equal (logic.ground-listp x)
         (if (consp x)
             (and (logic.groundp (car x))
                  (logic.ground-listp (cdr x)))
           t))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable logic.flag-groundp
                                    logic.groundp
                                    logic.ground-listp))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition logic.groundp))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition logic.ground-listp))))

(defthm logic.ground-listp-when-not-consp
  (implies (not (consp x))
           (equal (logic.ground-listp x)
                  t))
  :hints(("Goal" :in-theory (enable definition-of-logic.ground-listp))))

(defthm logic.ground-listp-of-cons
  (equal (logic.ground-listp (cons a x))
         (and (logic.groundp a)
              (logic.ground-listp x)))
  :hints(("Goal" :in-theory (enable definition-of-logic.ground-listp))))

(defthm booleanp-of-logic.ground-listp
  (equal (booleanp (logic.ground-listp x))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm booleanp-of-logic.groundp
  (equal (booleanp (logic.groundp x))
         t)
  :hints(("Goal" :in-theory (enable definition-of-logic.groundp))))

(defthm logic.groundp-when-logic.constantp
  (implies (logic.constantp x)
           (equal (logic.groundp x)
                  t))
  :hints(("Goal" :in-theory (enable definition-of-logic.groundp))))

(defthm forcing-logic.ground-listp-of-logic.function-args-when-logic.groundp
  (implies (and (logic.groundp x)
                (force (logic.functionp x)))
           (equal (logic.ground-listp (logic.function-args x))
                  t))
  :hints(("Goal" :in-theory (enable definition-of-logic.groundp))))

(defthm forcing-logic.ground-listp-of-logic.lambda-actuals-when-logic.groundp
  (implies (and (logic.groundp x)
                (force (logic.lambdap x)))
           (equal (logic.ground-listp (logic.lambda-actuals x))
                  t))
  :hints(("Goal" :in-theory (enable definition-of-logic.groundp))))



(deflist logic.ground-listp (x)
  (logic.groundp x)
  :elementp-of-nil nil
  :already-definedp t)

(defthm logic.ground-listp-when-logic.constant-listp
  (implies (logic.constant-listp x)
           (equal (logic.ground-listp x)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.groundp-of-logic.function
  (implies (and (force (logic.function-namep name))
                (force (true-listp args))
                (force (logic.term-listp args)))
           (equal (logic.groundp (logic.function name args))
                  (logic.ground-listp args)))
  :hints(("Goal" :in-theory (enable definition-of-logic.groundp))))

(defthm forcing-logic.groundp-of-logic.lambda
  (implies (and (force (true-listp formals))
                (force (logic.variable-listp formals))
                (force (uniquep formals))
                (force (logic.termp body))
                (force (subsetp (logic.term-vars body) formals))
                (force (equal (len formals) (len actuals)))
                (force (true-listp actuals))
                (force (logic.term-listp actuals)))
           (equal (logic.groundp (logic.lambda formals body actuals))
                  (logic.ground-listp actuals)))
  :hints(("Goal" :in-theory (enable definition-of-logic.groundp))))


;; Theorem: Suppose that x is some arbitrary term (perhaps with variables) and
;; sigma is substitution list which binds every variable mentioned in x to some
;; ground term.  Then, x/sigma is a ground term.

(defthmd lemma-2-for-forcing-logic.groundp-of-logic.substitute
  (implies (logic.ground-listp (range sigma))
           (equal (logic.groundp (cdr (lookup x sigma)))
                  (memberp x (domain sigma))))
  :hints(("Goal" :induct (cdr-induction sigma))))

(defthms-flag
  :shared-hyp (and (logic.sigmap sigma)
                   (logic.ground-listp (range sigma)))
  :thms ((term forcing-logic.groundp-of-logic.substitute
               (implies (and (logic.termp x)
                             (subsetp (logic.term-vars x) (domain sigma)))
                        (equal (logic.groundp (logic.substitute x sigma))
                               t)))
         (t forcing-logic.ground-listp-of-logic.substitute-list
            (implies (and (logic.term-listp x)
                          (subsetp (logic.term-list-vars x) (domain sigma)))
                     (equal (logic.ground-listp (logic.substitute-list x sigma))
                            t))))
  :hints (("Goal"
           :induct (logic.term-induction flag x)
           :in-theory (enable lemma-2-for-forcing-logic.groundp-of-logic.substitute))))



;; BOZO -- do we really want just logic.constant-listp in the following rules, or
;; would logic.ground-listp be better since it could still backchain to
;; logic.constant-listp?

(defthm forcing-logic.groundp-when-logic.constant-listp-of-logic.function-args
  (implies (and (logic.constant-listp (logic.function-args term))
                (force (logic.termp term))
                (force (logic.functionp term)))
           (equal (logic.groundp term)
                  t))
  :hints(("Goal"
          :use ((:instance forcing-logic.groundp-of-logic.function
                           (name (logic.function-name term))
                           (args (logic.function-args term)))))))

(defthm forcing-logic.groundp-when-logic.constant-listp-of-logic.lambda-actuals
  (implies (and (logic.constant-listp (logic.lambda-actuals term))
                (force (logic.termp term))
                (force (logic.lambdap term)))
           (equal (logic.groundp term)
                  t))
  :hints(("Goal"
          :use ((:instance forcing-logic.groundp-of-logic.lambda
                           (formals (logic.lambda-formals term))
                           (body    (logic.lambda-body term))
                           (actuals (logic.lambda-actuals term)))))))
