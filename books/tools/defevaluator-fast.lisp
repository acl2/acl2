; defevaluator-fast -- faster version of defevaluator
; Copyright (C) 2009-2014 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "ACL2")
(include-book "xdoc/top" :dir :system)
(program)

(defxdoc defevaluator-fast
  :parents (defevaluator)
  :short "Formerly a faster alternative to @(see defevaluator), now just an alias."
  :long "<p>See @(see defevaluator).  This used to be a higher-performance
reimplementation of defevaluator, but then defevaluator was changed to do
basically the same as this function, so we then changed this to just be an
alias for defevaluator.</p>")


(defmacro defevaluator-fast (&rest args)
  `(defevaluator . ,args))



(logic)

(local
 ;; A test to show that ACL2 recognizes evaluators defined with
 ;; DEFEVALUATOR-FAST as valid evaluators for meta-reasoning:
 (progn
   (defevaluator-fast foo-ev foo-ev-lst
     ((XXXJOIN FN ARGS)
      (INTEGER-ABS X)
      (OR-MACRO LST)
      (AND-MACRO LST)
      (LIST-MACRO LST)
      (TRUE-LISTP X)
      (EQ X Y)
      (REWRITE-EQUIV X)
      (HIDE X)
      (NOT P)
      (IMPLIES P Q)
      (BOOLEANP X)
      (XOR P Q)
      (IFF P Q)
      (O< X Y)
      (O-P X)
      (SYMBOLP X)
      (SYMBOL-PACKAGE-NAME X)
      (SYMBOL-NAME X)
      (STRINGP X)
      (REALPART X)
      (RATIONALP X)
      (PKG-WITNESS PKG)
      (NUMERATOR X)
      (INTERN-IN-PACKAGE-OF-SYMBOL STR SYM)
      (INTEGERP X)
      (IMAGPART X)
      (IF X Y Z)
      (EQUAL X Y)
      (DENOMINATOR X)
      (CONSP X)
      (CONS X Y)
      (COERCE X Y)
      (COMPLEX-RATIONALP X)
      (COMPLEX X Y)
      (CODE-CHAR X)
      (CHARACTERP X)
      (CHAR-CODE X)
      (CDR X)
      (CAR X)
      (< X Y)
      (UNARY-/ X)
      (UNARY-- X)
      (BINARY-+ X Y)
      (BINARY-* X Y)
      (BAD-ATOM<= X Y)
      (ACL2-NUMBERP X)))

   (defun stupid-cp (x)
     (list x))

   ;; ACL2 recognizes FOO-EV as a valid evaluator:
   (defthm stupid-cp-correct
     (implies (and (pseudo-term-listp cl)
                   (alistp a)
                   (foo-ev
                    (conjoin-clauses (stupid-cp cl))
                    a))
              (foo-ev
               (disjoin cl) a))
     :rule-classes :clause-processor)))

(local
 ;; A test to show that ACL2 recognizes evaluators defined with
 ;; DEFEVALUATOR-FAST as valid evaluators for meta-reasoning:
 (progn
   (defevaluator-fast foo2-ev foo2-ev-lst
     ((XXXJOIN FN ARGS)
      (INTEGER-ABS X)
      (OR-MACRO LST)
      (AND-MACRO LST)
      (LIST-MACRO LST)
      (TRUE-LISTP X)
      (EQ X Y)
      (REWRITE-EQUIV X)
      (HIDE X)
      (NOT P)
      (IMPLIES P Q)
      (BOOLEANP X)
      (XOR P Q)
      (IFF P Q)
      (O< X Y)
      (O-P X)
      (SYMBOLP X)
      (SYMBOL-PACKAGE-NAME X)
      (SYMBOL-NAME X)
      (STRINGP X)
      (REALPART X)
      (RATIONALP X)
      (PKG-WITNESS PKG)
      (NUMERATOR X)
      (INTERN-IN-PACKAGE-OF-SYMBOL STR SYM)
      (INTEGERP X)
      (IMAGPART X)
      (IF X Y Z)
      (EQUAL X Y)
      (DENOMINATOR X)
      (CONSP X)
      (CONS X Y)
      (COERCE X Y)
      (COMPLEX-RATIONALP X)
      (COMPLEX X Y)
      (CODE-CHAR X)
      (CHARACTERP X)
      (CHAR-CODE X)
      (CDR X)
      (CAR X)
      (< X Y)
      (UNARY-/ X)
      (UNARY-- X)
      (BINARY-+ X Y)
      (BINARY-* X Y)
      (BAD-ATOM<= X Y)
      (ACL2-NUMBERP X))
     :namedp t)

   (defun stupid-cp2 (x)
     (list x))

   ;; ACL2 recognizes FOO-EV as a valid evaluator:
   (defthm stupid-cp2-correct
     (implies (and (pseudo-term-listp cl)
                   (alistp a)
                   (foo2-ev
                    (conjoin-clauses (stupid-cp cl))
                    a))
              (foo2-ev
               (disjoin cl) a))
     :rule-classes :clause-processor)))





(defun mk-defeval-entries (fns world)
  (if (atom fns)
      nil
    (let ((formals (getprop (car fns) 'formals nil 'current-acl2-world world)))
      (cons (cons (car fns) formals)
            (mk-defeval-entries (cdr fns) world)))))



#||

;; Infrastructure for testing this
(defun all-syms-in-world (w)
  (remove-duplicates (strip-cars w)))

(defun list-of-nilsp (x)
  (if (atom x)
      (eq x nil)
    (and (eq (car x) nil)
         (list-of-nilsp (cdr x)))))

(defun logic-function-syms (syms world)
  (if (atom syms)
      nil
    (if (and (not (eq (getprop (car syms) 'formals :none 'current-acl2-world
                               world)
                      :none))
             (member (getprop (car syms) 'symbol-class nil 'current-acl2-world world)
                     '(:ideal :common-lisp-compliant))
             (not (member (car syms)
                          (global-val 'untouchable-fns world)))
             (not (member (car syms) '(synp must-be-equal
                                            open-output-channel!)))
             (list-of-nilsp (fgetprop (car syms) 'stobjs-out nil
                                      world))
             (list-of-nilsp (fgetprop (car syms) 'stobjs-in nil
                                      world))
             (not (and (member (car syms) *ec-call-bad-ops*)
                       (not (equal (fgetprop (car syms) 'guard ''t
                                             world)
                                   ''t)))))
        (cons (car syms) (logic-function-syms (cdr syms) world))
      (logic-function-syms (cdr syms) world))))

(defun mk-defeval-entries (fns world)
  (if (atom fns)
      nil
    (let ((formals (getprop (car fns) 'formals nil 'current-acl2-world world)))
      (cons (cons (car fns) formals)
            (mk-defeval-entries (cdr fns) world)))))



(logic)

(make-event
 `(defconst *defeval-entries-for-all-reasonable-functions*
    ',(let ((world (w state)))
        (mk-defeval-entries (logic-function-syms (all-syms-in-world world)
                                                world)
                            world))))



(time$
 (make-event
  `(defevaluator-fast test-defevaluator-fast-ev test-defevaluator-fast-ev-lst
     ,*defeval-entries-for-all-reasonable-functions*)))
;; 2.2 sec with output off, 6.0 sec with output on







;; For comparison, testing with the original defevaluator (plus a couple of
;; trivial mods:)

(defttag blah)

;; Redefining the usual defevaluator so that it uses :non-executable t.
(redef!)

(defun defevaluator-form (evfn evfn-lst fn-args-lst)
  (declare (xargs :mode :program))
  (let* ((clauses (evaluator-clauses evfn evfn-lst fn-args-lst))
         (fns-clauses (defevaluator-form/fns-clauses evfn fn-args-lst))
         (defthms (defevaluator-form/defthms
                    evfn
                    (symbol-name (pack2 evfn '-constraint-))
                    0
                    clauses)))
    `(encapsulate
      (((,evfn * *) => *)
       ((,evfn-lst * *) => *))
      (set-inhibit-warnings "theory")
      (local (in-theory *defevaluator-form-base-theory*))
      ,@(sublis
         (list (cons 'evfn evfn)
               (cons 'evfn-lst evfn-lst)
               (cons 'fns-clauses fns-clauses)
               (cons 'defthms defthms))
         '((local
            (mutual-recursion
; MODIFIED: Make the evaluator non-executable so it can handle stobjs and mvs
             (defun-nx evfn (x a)
               (declare (xargs :verify-guards nil
                               :measure (acl2-count x)
                               :well-founded-relation o<
                               :mode :logic
; MODIFIED: Prevent preprocessing in the measure theorem to eliminate a drastic
; slowdown.
                               :hints (("Goal" :do-not '(preprocess)))))
               (cond
                ((symbolp x) (and x (cdr (assoc-eq x a))))
                ((atom x) nil)
                ((eq (car x) 'quote) (car (cdr x)))
                ((consp (car x))
                 (evfn (car (cdr (cdr (car x))))
                       (pairlis$ (car (cdr (car x)))
                                 (evfn-lst (cdr x) a))))
                .
                fns-clauses))
             (defun evfn-lst (x-lst a)
               (declare (xargs :measure (acl2-count x-lst)
                               :well-founded-relation o<))
               (cond ((endp x-lst) nil)
                     (t (cons (evfn (car x-lst) a)
                              (evfn-lst (cdr x-lst) a)))))))
           (local
            (defthm eval-list-kwote-lst
              (equal (evfn-lst (kwote-lst args) a)
                     (fix-true-list args))))
           . defthms)))))

(set-inhibit-output-lst '(proof-tree prove event expansion))

(time$
 (make-event
  `(defevaluator test-defevaluator-ev test-defevaluator-ev-lst
     ,(take 80 *defeval-entries-for-all-reasonable-functions*))))


(defthm fix-true-list-test-defevaluator-fast-ev-lst
  (equal (fix-true-list (test-defevaluator-fast-ev-lst x a))
         (test-defevaluator-fast-ev-lst x a))
  :hints (("goal" :induct (len x)
           :in-theory (e/d ((:induction len))
                           (test-defevaluator-fast-ev-commutes-car)))))

(defthm test-defevaluator-fast-ev-commutes-car
  (equal (test-defevaluator-fast-ev (car x) a)
         (car (test-defevaluator-fast-ev-lst x a))))

(defthm test-defevaluator-fast-ev-lst-commutes-cdr
  (equal (cdr (test-defevaluator-fast-ev-lst x a))
         (test-defevaluator-fast-ev-lst (cdr x) a))
  :hints(("Goal" :in-theory (disable test-defevaluator-fast-ev-commutes-car))))


:trans1 (defevaluator-fast fooev fooevl
  ((if a b c)
   (cons a b)
   (consp a)
   (car a)
   (car b)
   (binary-append c d)
   (nth n x)
   (mv-nth n x)))


(SET-INHIBIT-WARNINGS "theory")
(LOCAL (IN-THEORY *DEFEVALUATOR-FAST-FORM-BASE-THEORY*))
(LOCAL
 (MUTUAL-RECURSION
  (DEFUN-NX FOOEV (X A)
    (DECLARE (XARGS :VERIFY-GUARDS NIL
                    :MEASURE (ACL2-COUNT X)
                    :WELL-FOUNDED-RELATION O<
                    :NORMALIZE NIL
                    :MODE :LOGIC))
    (COND ((SYMBOLP X)
           (AND X (CDR (ASSOC-EQ X A))))
          ((ATOM X) NIL)
          ((EQ (CAR X) 'QUOTE) (CAR (CDR X)))
          (T (LET ((ARGS (FOOEVL (CDR X) A)))
                  (COND ((CONSP (CAR X))
                         (FOOEV (CAR (CDR (CDR (CAR X))))
                                (PAIRLIS$ (CAR (CDR (CAR X))) ARGS)))
                        ((EQUAL (CAR X) 'IF)
                         (IF (CAR ARGS)
                             (CAR (CDR ARGS))
                             (CAR (CDR (CDR ARGS)))))
                        ((EQUAL (CAR X) 'CONS)
                         (CONS (CAR ARGS) (CAR (CDR ARGS))))
                        ((EQUAL (CAR X) 'CONSP)
                         (CONSP (CAR ARGS)))
                        ((EQUAL (CAR X) 'CAR) (CAR (CAR ARGS)))
                        ((EQUAL (CAR X) 'CAR) (CAR (CAR ARGS)))
                        ((EQUAL (CAR X) 'BINARY-APPEND)
                         (BINARY-APPEND (CAR ARGS)
                                        (CAR (CDR ARGS))))
                        ((EQUAL (CAR X) 'NTH)
                         (NTH (CAR ARGS) (CAR (CDR ARGS))))
                        ((EQUAL (CAR X) 'MV-NTH)
                         (MV-NTH (CAR ARGS) (CAR (CDR ARGS))))
                        (T NIL))))))
  (DEFUN FOOEVL (X-LST A)
    (DECLARE (XARGS :MEASURE (ACL2-COUNT X-LST)
                    :WELL-FOUNDED-RELATION O<))
    (COND ((ENDP X-LST) NIL)
          (T (CONS (FOOEV (CAR X-LST) A)
                   (FOOEVL (CDR X-LST) A)))))))
(LOCAL (IN-THEORY (DISABLE FOOEV FOOEVL)))
(LOCAL
 (DEFTHM EVAL-LIST-KWOTE-LST
   (EQUAL (FOOEVL (KWOTE-LST ARGS) A)
          (FIX-TRUE-LIST ARGS))
   :HINTS (("goal" :EXPAND ((:FREE (X Y) (FOOEVL (CONS X Y) A))
                            (FOOEVL NIL A)
                            (:FREE (X) (FOOEV (LIST 'QUOTE X) A)))
            :IN-THEORY (ENABLE TRUE-LIST-FIX)
            :INDUCT (TRUE-LIST-FIX ARGS)))))
(LOCAL (DEFTHM FIX-TRUE-LIST-EV-LST
         (EQUAL (FIX-TRUE-LIST (FOOEVL X A))
                (FOOEVL X A))
         :HINTS (("goal" :INDUCT (LEN X)
                  :IN-THEORY (E/D ((:INDUCTION LEN)))
                  :EXPAND ((FOOEVL X A) (FOOEVL NIL A))))))
(LOCAL (DEFTHM EV-COMMUTES-CAR
         (EQUAL (CAR (FOOEVL X A))
                (FOOEV (CAR X) A))
         :HINTS (("goal" :EXPAND ((FOOEVL X A) (FOOEV NIL A))
                  :IN-THEORY (ENABLE DEFAULT-CAR)))))
(LOCAL (DEFTHM EV-LST-COMMUTES-CDR
         (EQUAL (CDR (FOOEVL X A))
                (FOOEVL (CDR X) A))
         :HINTS (("Goal" :EXPAND ((FOOEVL X A) (FOOEVL NIL A))
                  :IN-THEORY (ENABLE DEFAULT-CDR)))))



(DEFTHM FOOEV-CONSTRAINT-2
          (IMPLIES (AND (CONSP X) (EQUAL (CAR X) 'QUOTE))
                   (EQUAL (FOOEV X A) (CADR X)))
          :HINTS (("goal" :EXPAND ((FOOEV X A)))))

(local (defthm fooev-lst-kwote-lst
         (equal (fooev-lst (kwote-lst x)

(DEFTHMD FOOEV-CONSTRAINT-0
  (IMPLIES (AND (CONSP X)
                (SYNTAXP (NOT (EQUAL A ''NIL)))
                (NOT (EQUAL (CAR X) 'QUOTE)))
           (EQUAL (FOOEV X A)
                  (FOOEV (CONS (CAR X)
                               (KWOTE-LST (FOOEVL (CDR X) A)))
                         NIL)))
  :HINTS (("Goal" :EXPAND ((:FREE (X) (HIDE X))
                           (FOOEV X A)
                           (:FREE (ARGS)
                                  (FOOEV (CONS (CAR X) ARGS) NIL)))
           :in-theory (e/d** (eval-list-kwote-lst
                              fix-true-list-ev-lst
                              car-cons cdr-cons)))))


||#
