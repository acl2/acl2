; Helper rules about cterm-ev, an evaluator that knows the functions cons-term evaluates
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

; cert_param: (non-acl2r)

;; CTERM-EV, from sublis-var-meaning.lisp, knows about all the primitives that
;; CONS-TERM may evaluate when given constant arguments.  So it is the natural
;; evaluator for stating the correctness of system functions that build terms
;; using CONS-TERM.  Since CTERM-EV is introduced by DEFEVALUATOR, theorems
;; about it can be functionally instantiated to any evaluator that knows about
;; at least those functions.

(include-book "clause-processors/sublis-var-meaning" :dir :system)
(include-book "kestrel/terms-light/free-vars-in-term" :dir :system)
(include-book "kestrel/alists-light/alists-equiv-on" :dir :system)
(local (include-book "kestrel/terms-light/empty-eval-helpers" :dir :system))
(local (include-book "helpers"))
(local (include-book "kestrel/alists-light/strip-cars" :dir :system))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))

;; If the alists agree on some set of keys that includes all the free vars in
;; the term, then the evaluations give the same result.
(defthm equal-of-cterm-ev-and-cterm-ev-when-alists-equiv-on
  (implies (and (alists-equiv-on keys alist1 alist2)
                (subsetp-equal (free-vars-in-term term) keys)
                (pseudo-termp term))
           (equal (equal (cterm-ev term alist1)
                         (cterm-ev term alist2))
                  t))
  :hints (("Goal" :in-theory (enable cterm-ev-of-fncall-args)
           :use (:functional-instance equal-of-empty-eval-and-empty-eval-when-alists-equiv-on-alt
                                      (empty-eval cterm-ev)
                                      (empty-eval-list cterm-ev-lst)))))

(defthm cterm-ev-of-cdr-of-assoc-equal-of-pairlis$
  (equal (cterm-ev (cdr (assoc-equal key (pairlis$ vars terms))) a)
         (cdr (assoc-equal key (pairlis$ vars (cterm-ev-lst terms a)))))
  :hints (("Goal" :in-theory (enable pairlis$ assoc-equal))))

;; Evaluating a closed lambda body in an extended alist is the same as
;; evaluating it in an alist binding just the lambda formals.
(defthm cterm-ev-of-append-of-pairlis$-when-closed
  (implies (and (subsetp-equal (free-vars-in-term body) formals)
                (pseudo-termp body))
           (equal (cterm-ev body (append (pairlis$ formals vals) a))
                  (cterm-ev body (pairlis$ formals vals))))
  :hints (("Goal" :use (:instance equal-of-cterm-ev-and-cterm-ev-when-alists-equiv-on
                                  (term body)
                                  (keys formals)
                                  (alist1 (append (pairlis$ formals vals) a))
                                  (alist2 (pairlis$ formals vals)))
           :in-theory (disable equal-of-cterm-ev-and-cterm-ev-when-alists-equiv-on))))
