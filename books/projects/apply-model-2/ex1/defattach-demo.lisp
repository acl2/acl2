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

(defthm evaluation-by-rewriting
  (implies (warrant square)
           (equal (sumlist '(1 2 3) 'square)
                  14))
  :hints (("Goal" :expand ((:free (x) (HIDE x))))))

(expected-to :fail :current
             (sumlist '(1 2 3) 'square)
             14)

(expected-to :succeed :evaluation
             (sumlist '(1 2 3) 'square)
             14)

(expected-to :succeed :evaluation
             (sumlist '((1 2 3) (4 5 6))
                      '(lambda (lst) (sumlist lst 'square)))
             91)

