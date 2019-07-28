; Copyright (C) 2019, ForrestHunt, Inc.
; Written by Matt Kaufmann and J Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Demonstration of Defattach for BADGE-USERFN and APPLY$-USERFN
; Matt Kaufmann and J Moore

; This book demonstrates that we can successfully attach the doppelgangers of
; the functions in user-defs.lisp to the badge-userfn and apply$-userfn.

; That in itself is not a hard goal to achieve since the constraints on the
; stubs are so weak.  But, as briefly illustrated below, these particular
; choices of our attachments give us the ability to evaluate the mapping
; functions of user-defs.lisp and get the expected results.

; We cite this as evidence that the ACL2 source code (which does analogous
; defattaches) is both permitted and produces a reasonable evaluation theory.

(in-package "MODAPP")
(include-book "user-defs")
(include-book "doppelgangers")
(include-book "misc/eval" :dir :system)

(defthm take-n-take-n
  (implies (natp n)
           (equal (take n (take n lst))
                  (take n lst))))

(defattach
  (apply$-userfn apply$-userfn!)
  (untame-apply$ untame-apply$!)
  (badge-userfn badge-userfn!)
  :hints (("Goal" :expand ((:free (fn args) (apply$-userfn1! fn args))))))

; The rest of this book just sets up a few simple tests of the resulting
; evaluation theory.

(defmacro expected-to (expectation theory form val)

; This macro is just a convenient way of evaluating the translation of form in
; either the current theory or the evaluation theory and testing whether the
; result is val.  The result can thus fail in two ways: (a) form's translation
; and/or evaluation causes an error or (b) form's translation and evaluation
; return a value different from val.  Expectation is :fail or :succeed and
; indicates whether we expect the evaluation to fail or succeed.  Theory is
; either :current or :evaluation.

  `(,(if (eq expectation :fail) 'acl2::must-fail 'acl2::must-succeed)
    (er-let*
      ((pair (acl2::simple-translate-and-eval
              ',form
              nil nil "Help!" 'ctx (w state) state
              ,(if (eq theory :current) nil t) ; = aok
              )))
      (cond
       ((equal (cdr pair) ,val) (value t))
       (t (mv t nil state))))))

; Because apply$ is not evaluable in the current theory, the following will fail.

(expected-to :fail :current
             (collect '((1 2 3) (4 5 6))
                      '(lambda (x)
                         (COLLECT (MY-REV x)
                                  '(lambda (y) (cons 'a y)))))
             '(((A . 3) (A . 2) (A . 1))
               ((A . 6) (A . 5) (A . 4))))

; However, the equivalence can be proved in the current theory if we have the
; right warrants:

(defthm demo-of-collect-eval-by-rewriting
  (implies (and (apply$-warrant-COLLECT)
                (apply$-warrant-MY-REV))
           (equal (collect '((1 2 3) (4 5 6))
                           '(LAMBDA (X)
                              (COLLECT (MY-REV X)
                                       '(LAMBDA (Y) (CONS 'A Y)))))
                  '(((A . 3) (A . 2) (A . 1))
                    ((A . 6) (A . 5) (A . 4)))))
  :hints (("Goal" :expand ((:free (x) (HIDE x))))))

; The warrants for COLLECT and MY-REV are necessary because those symbols appear
; inside the quoted LAMBDA and are thus ultimately apply$'d.  (The collect
; outside the LAMBDA is just part of an ACL2 term, not something concerning
; apply$ or ev$.

; While we cannot evaluate the collect expression above in the current theory
; we can do so in the evaluation theory because we've done the defattaches in
; the portcullis.

(expected-to :succeed :evaluation
             (collect '((1 2 3) (4 5 6))
                      '(LAMBDA (X)
                         (COLLECT (MY-REV X)
                                  '(LAMBDA (Y) (CONS 'A Y)))))
             '(((A . 3) (A . 2) (A . 1))
               ((A . 6) (A . 5) (A . 4))))

; Here is another sample evaluation in the evaluation theory, this
; time using collect and FOLDR.

(expected-to :succeed :evaluation
             (collect '((1) (1 2) (1 2 3) (1 2 3 4 5))
                      '(LAMBDA (LST) (FOLDR LST 'BINARY-* '1)))
             '(1 2 6 120))

; This is an example we also used in user-thms.lisp showing that we could pass
; COLLECT as the funtional arg to a mapping function and have it get its
; functional arg from the data -- provided the data contains tame functional
; arguments.

(expected-to :succeed :evaluation
             (collect* '(((1 2 3) (LAMBDA (X) (CONS 'A X)))
                         ((4 5 6 7) SQUARE)
                         (((20 21 22)
                           (30 31 32)
                           (40 41 42))
                          (LAMBDA (Y)
                                  (COLLECT Y '(LAMBDA (Z) (CONS 'C Z)))))
                         )
                       'COLLECT)
             '(((A . 1)(A . 2)(A . 3))
               (16 25 36 49)
               (((C . 20) (C . 21) (C . 22))
                ((C . 30) (C . 31) (C . 32))
                ((C . 40) (C . 41) (C . 42)))
               ))


; Expt-2-and-expt-3 has no warrant.  So (badge 'EXPT-2-EXPT-3) is not what you
; might expect (even though a badge for it is recorded in the badge-table).  In
; fact, calling badge on 'EXPT-2-AND-EXPT-3 causes an evaluation error.

(expected-to :fail :evaluation
             (badge 'EXPT-2-AND-EXPT-3)
             '(APPLY$-BADGE NIL 1 . T))

(expected-to :succeed :evaluation
             (badge 'expt-5)
             '(APPLY$-BADGE 1 1 . T))

