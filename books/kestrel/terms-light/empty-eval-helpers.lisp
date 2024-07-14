; Rules about the empty evaluator (which we use a lot in this dir)
;
; Copyright (C) 2023-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/evaluators/empty-eval" :dir :system) ; move to a proofs book

(include-book "non-trivial-formals")
(include-book "trivial-formals")
(include-book "kestrel/alists-light/alists-equiv-on" :dir :system)
(local (include-book "helpers"))
(local (include-book "kestrel/lists-light/no-duplicatesp-equal" :dir :system))
(local (include-book "kestrel/alists-light/alistp" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/alists-light/pairlis-dollar" :dir :system))
(local (include-book "kestrel/alists-light/strip-cars" :dir :system))

(defthm cdr-of-assoc-equal-of-pairlis$-of-empty-eval-list-when-member-equal-of-trivial-formals
  (implies (and (member-equal var (trivial-formals formals args))
     ;               (member-equal var formals)  ;drop?
     ;              (symbol-listp formals)
                (no-duplicatesp-equal formals)
                var
                (symbolp var))
           (equal (cdr (assoc-equal var (pairlis$ formals (empty-eval-list args a))))
                  (cdr (assoc-equal var a)) ; (empty-eval var a)
                  ))
  :hints (("Goal" :in-theory (enable trivial-formals pairlis$))))

;; slight rephrasing of the above
(defthm cdr-of-assoc-equal-of-pairlis$-of-empty-eval-list-when-not-member-equal-of-non-trivial-formals
  (implies (and (not (member-equal var (non-trivial-formals formals args)))
                (member-equal var formals)
     ;              (symbol-listp formals)
                (no-duplicatesp-equal formals)
                var
                (symbolp var))
           (equal (cdr (assoc-equal var (pairlis$ formals (empty-eval-list args a))))
                  (cdr (assoc-equal var a)) ; (empty-eval var a)
                  ))
  :hints (("Goal" :in-theory (enable trivial-formals pairlis$))))

(defthm helper1
  (implies (and (not (intersection-equal vars (non-trivial-formals formals args)))
                (no-duplicatesp-equal formals)
                (symbol-listp formals)
                (symbol-listp vars)
                (not (member-equal nil vars)))
           (alists-equiv-on vars
                            (append (pairlis$ formals (empty-eval-list args a)) a)
                            a))
  :hints (("Goal" :in-theory (enable alists-equiv-on symbol-listp intersection-equal))))

;(local (in-theory (disable symbol-listp no-duplicatesp-equal)))

;dup!
(defthmd lookup-equal-of-pairlis$-of-empty-eval-list
  (equal (lookup-equal b (pairlis$ formals (empty-eval-list args a)))
         (empty-eval (lookup-equal b (pairlis$ formals args)) a))
  :hints (("Goal" :in-theory (enable pairlis$))))
