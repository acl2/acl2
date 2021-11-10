; A utility to recognize a conjunction

; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/forms" :dir :system)
(include-book "kestrel/evaluators/if-eval" :dir :system)

(defund term-is-conjunctionp (term)
  (declare (xargs :guard (pseudo-termp term)))
  (and (call-of 'if term)
       (= 3 (len (fargs term)))
       (equal *nil* (farg3 term)) ; (if x y nil)
       ))

(defthm term-is-conjunctionp-forward-to-consp
  (implies (term-is-conjunctionp term)
           (consp term))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable term-is-conjunctionp))))

(defthm term-is-conjunctionp-forward-to-pseudo-termp-of-cadr
  (implies (and (term-is-conjunctionp term)
                (pseudo-termp term))
           (pseudo-termp (cadr term)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable term-is-conjunctionp))))

(defthm term-is-conjunctionp-forward-to-pseudo-termp-of-caddr
  (implies (and (term-is-conjunctionp term)
                (pseudo-termp term))
           (pseudo-termp (caddr term)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable term-is-conjunctionp))))

(defthm if-eval-when-term-is-conjunctionp
  (implies (term-is-conjunctionp conj)
           (iff (if-eval conj a)
                (and (if-eval (farg1 conj) a)
                     (if-eval (farg2 conj) a))))
  :hints (("Goal" :in-theory (enable term-is-conjunctionp))))

(defthm if-eval-of-cadddr-when-term-is-conjunctionp-forward
  (implies (and (not (if-eval (caddr conj) a))
                (term-is-conjunctionp conj))
           (not (if-eval conj a)))
  :rule-classes :forward-chaining)

(defthm if-eval-of-cadddr-when-term-is-conjunctionp
  (implies (and (if-eval conj a)
                (term-is-conjunctionp conj))
         (if-eval (caddr conj) a)))
