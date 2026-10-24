; An evaluator for stating the correctness of generalization
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; GENERALIZE-EV knows all the functions that CONS-TERM may evaluate on
;; constant arguments (the same functions as CTERM-EV in
;; clause-processors/sublis-var-meaning.lisp), together with IF, NOT, and IFF,
;; which add-literal treats specially.

(include-book "kestrel/evaluators/defevaluator-plus" :dir :system)
(include-book "kestrel/evaluators/defevaluator-theorems" :dir :system)
(include-book "clause-processors/sublis-var-meaning" :dir :system)

(defevaluator+ generalize-ev
  acl2-numberp binary-* binary-+ unary-- unary-/ < car cdr char-code characterp
  code-char complex complex-rationalp coerce cons consp denominator equal
  imagpart integerp intern-in-package-of-symbol numerator rationalp realpart
  stringp symbol-name symbol-package-name symbolp if not iff)

(defevaluator-theorems generalize-ev generalize-ev-list)

;; Evaluates the terms in the range of ALIST.
(defun generalize-ev-alist (alist a)
  (if (atom alist)
      nil
    (cons (cons (caar alist) (generalize-ev (cdar alist) a))
          (generalize-ev-alist (cdr alist) a))))

(defthm generalize-ev-of-sublis-var
  (implies (and (pseudo-termp x)
                (not (assoc-equal nil alist)))
           (equal (generalize-ev (sublis-var alist x) a)
                  (generalize-ev x (append (generalize-ev-alist alist a) a))))
  :hints (("Goal" :use (:functional-instance eval-of-sublis-var
                                             (cterm-ev generalize-ev)
                                             (cterm-ev-lst generalize-ev-list)
                                             (cterm-ev-alist generalize-ev-alist)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (generalize-ev-of-fncall-args) (generalize-ev-of-fncall-args-back))))))

(defthm generalize-ev-of-cons-term
  (equal (generalize-ev (cons-term fn args) a)
         (generalize-ev (cons fn args) a))
  :hints (("Goal" :use (:functional-instance cterm-ev-cons-term-correct
                                             (cterm-ev generalize-ev)
                                             (cterm-ev-lst generalize-ev-list)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (generalize-ev-of-fncall-args) (generalize-ev-of-fncall-args-back))))))
