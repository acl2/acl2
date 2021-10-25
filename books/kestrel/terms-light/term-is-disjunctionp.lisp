; A utility to recognize a disjunction

; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/forms" :dir :system)
(include-book "kestrel/evaluators/if-and-not-eval" :dir :system)

;todo: use more
(defund term-is-disjunctionp (term)
  (declare (xargs :guard (pseudo-termp term)))
  (and (call-of 'if term)
       (= 3 (len (fargs term)))
       (or (equal *t* (farg2 term)) ; (if x t y)
           (equal (farg1 term) (farg2 term))) ; (if x x y)
       ))

(defthm term-is-disjunctionp-forward-to-equal-of-len-of-fargs
  (implies (term-is-disjunctionp term)
           (equal 3 (len (fargs term))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable term-is-disjunctionp))))

(defthm term-is-disjunctionp-forward-to-consp
  (implies (term-is-disjunctionp term)
           (consp term))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable term-is-disjunctionp))))

(defthm if-and-not-eval-when-term-is-disjunctionp
  (implies (term-is-disjunctionp disj)
           (iff (if-and-not-eval disj a)
                (or (if-and-not-eval (farg1 disj) a)
                    (if-and-not-eval (farg3 disj) a))))
  :hints (("Goal" :in-theory (enable term-is-disjunctionp))))

(defthm if-and-not-eval-of-cadddr-when-term-is-disjunctionp-forward
  (implies (and (if-and-not-eval (cadddr disj) a)
                (term-is-disjunctionp disj))
           (if-and-not-eval disj a))
  :rule-classes :forward-chaining)
