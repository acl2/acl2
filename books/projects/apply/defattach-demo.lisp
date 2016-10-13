; Copyright (C) 2016, ForrestHunt, Inc.
; Written by Matt Kaufmann and J Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Portcullis:
; (include-book "user-book")
; (include-book "doppelgangers")
; (defattach badge-userfn badge-userfn!)
; (defattach apply$-userfn apply$-userfn!)

; A Demonstration of the Evaluation Theory Produced by the Defattaches Above

(in-package "ACL2")

; This book demonstrates that we can successfully attach the doppelgangers to
; the four apply$ stubs.  Of course, that is not a hard goal to achieve since
; the constraints on the stubs are so weak.  But the defattaches below justify
; our later consideration of an evaluation theory containing the four
; corresponding attachment equations.  After the four attachments we show that
; a couple of examples evaluate as we expect.

(defmacro expected-to (expectation theory form val)

; This macro is just a convenient way of evaluating the translation of form in
; either the current theory or the evaluation theory and testing whether the
; result is val.  The result can thus fail in two ways: (a) form's translation
; and/or evaluation causes an error or (b) form's translation and evaluation
; return a value different from val.  Expectation is :fail or :succeed and
; indicates whether we expect the evaluation to fail or succeed.  Theory is
; either :current or :evaluation.

  `(,(if (eq expectation :fail) 'must-fail 'must-succeed)
    (er-let*
      ((pair (simple-translate-and-eval
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
                         (COLLECT (REV x)
                                  '(lambda (y) (cons 'a y)))))
             '(((A . 3) (A . 2) (A . 1))
               ((A . 6) (A . 5) (A . 4))))

; However, the equivalence can be proved in the current theory if we have the
; right warrants:

(defthm demo-of-collect-eval-by-rewriting
  (implies (and (apply$-warrant-COLLECT)
                (apply$-warrant-REV))
           (equal (collect '((1 2 3) (4 5 6))
                           '(LAMBDA (X)
                              (COLLECT (REV X)
                                       '(LAMBDA (Y) (CONS 'A Y)))))
                  '(((A . 3) (A . 2) (A . 1))
                    ((A . 6) (A . 5) (A . 4)))))
  :hints (("Goal" :expand ((:free (x) (HIDE x))))))

; The warrants for COLLECT and REV are necessary because those symbols appear
; inside the quoted LAMBDA and are thus ultimately apply$'d.  (The collect
; outside the LAMBDA is just part of an ACL2 term, not something concerning
; apply$ or ev$.

; While we cannot evaluate the collect expression above in the current theory
; we can do so in the evaluation theory because we've done the defattaches in
; the portcullis.

(expected-to :succeed :evaluation
             (collect '((1 2 3) (4 5 6))
                      '(LAMBDA (X)
                         (COLLECT (REV X)
                                  '(LAMBDA (Y) (CONS 'A Y)))))
             '(((A . 3) (A . 2) (A . 1))
               ((A . 6) (A . 5) (A . 4))))

; Here is another sample evaluation in the evaluation theory, this
; time using collect and FOLDR.

(expected-to :succeed :evaluation
             (collect '((1) (1 2) (1 2 3) (1 2 3 4 5))
                      '(LAMBDA (LST) (FOLDR LST 'BINARY-* '1)))
             '(1 2 6 120))

; Expt-2-and-expt-3 has no warrant.  So (badge 'EXPT-2-EXPT-3) is not what you
; might expect (even though a badge for it is recorded in the badge-table).  In
; fact, calling badge on 'EXPT-2-AND-EXPT-3 causes an evaluation error.

(expected-to :fail :evaluation
             (badge 'EXPT-2-AND-EXPT-3)
             '(APPLY$-BADGE NIL 1 . T))

(expected-to :succeed :evaluation
             (badge 'expt-5)
             '(APPLY$-BADGE T 1 . T))

